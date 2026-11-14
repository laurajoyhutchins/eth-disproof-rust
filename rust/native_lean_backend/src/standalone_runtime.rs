//! Standalone, dependency-free value semantics for a precisely supported
//! subset of Lean 4.34.1 runtime primitives. This module is embedded verbatim
//! in generated Rust only when the original IR requires object values.
//! All arithmetic is exact, not a u64 substitution for Nat/Int.
use std::cmp::Ordering;
use std::fmt;
use std::str::FromStr;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BigNat(Vec<u32>);

impl BigNat {
    pub fn from_u64(n: u64) -> Self {
        Self::normalize(vec![n as u32, (n >> 32) as u32])
    }

    fn normalize(mut digits: Vec<u32>) -> Self {
        while digits.last() == Some(&0) {
            digits.pop();
        }
        Self(digits)
    }

    pub fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    fn multiply_small(&self, factor: u32) -> Self {
        let mut digits = Vec::with_capacity(self.0.len() + 1);
        let mut carry = 0_u64;
        for &digit in &self.0 {
            let product = u64::from(digit) * u64::from(factor) + carry;
            digits.push(product as u32);
            carry = product >> 32;
        }
        if carry != 0 {
            digits.push(carry as u32);
        }
        Self::normalize(digits)
    }

    fn add_small(&self, extra: u32) -> Self {
        let mut digits = self.0.clone();
        let mut carry = u64::from(extra);
        for digit in &mut digits {
            let value = u64::from(*digit) + carry;
            *digit = value as u32;
            carry = value >> 32;
            if carry == 0 {
                break;
            }
        }
        if carry != 0 {
            digits.push(carry as u32);
        }
        Self::normalize(digits)
    }

    pub fn add(&self, other: &Self) -> Self {
        let mut digits = Vec::with_capacity(self.0.len().max(other.0.len()) + 1);
        let mut carry = 0_u64;
        for i in 0..self.0.len().max(other.0.len()) {
            let a = u64::from(*self.0.get(i).unwrap_or(&0));
            let b = u64::from(*other.0.get(i).unwrap_or(&0));
            let sum = a + b + carry;
            digits.push(sum as u32);
            carry = sum >> 32;
        }
        if carry != 0 {
            digits.push(carry as u32);
        }
        Self::normalize(digits)
    }

    fn cmp_magnitude(&self, other: &Self) -> Ordering {
        match self.0.len().cmp(&other.0.len()) {
            Ordering::Equal => self.0.iter().rev().cmp(other.0.iter().rev()),
            comparison => comparison,
        }
    }

    /// Truncated subtraction, matching Lean Nat.sub.
    pub fn sub(&self, other: &Self) -> Self {
        if self.cmp_magnitude(other) != Ordering::Greater {
            return Self::default();
        }
        self.sub_nonnegative(other)
    }

    fn sub_nonnegative(&self, other: &Self) -> Self {
        debug_assert!(self.cmp_magnitude(other) != Ordering::Less);
        let mut digits = Vec::with_capacity(self.0.len());
        let mut borrow = 0_i64;
        for i in 0..self.0.len() {
            let x = i64::from(self.0[i]);
            let y = i64::from(*other.0.get(i).unwrap_or(&0));
            let diff = x - y - borrow;
            if diff < 0 {
                digits.push((diff + (1_i64 << 32)) as u32);
                borrow = 1;
            } else {
                digits.push(diff as u32);
                borrow = 0;
            }
        }
        debug_assert_eq!(borrow, 0);
        Self::normalize(digits)
    }

    pub fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::default();
        }
        let mut digits = vec![0_u32; self.0.len() + other.0.len()];
        for (i, &lhs) in self.0.iter().enumerate() {
            let mut carry = 0_u64;
            for (j, &rhs) in other.0.iter().enumerate() {
                let idx = i + j;
                let product = u64::from(lhs) * u64::from(rhs) + u64::from(digits[idx]) + carry;
                digits[idx] = product as u32;
                carry = product >> 32;
            }
            digits[i + other.0.len()] = carry as u32;
        }
        Self::normalize(digits)
    }

    fn div_rem_small(&mut self, divisor: u32) -> u32 {
        let mut remainder = 0_u64;
        for digit in self.0.iter_mut().rev() {
            let value = (remainder << 32) | u64::from(*digit);
            *digit = (value / u64::from(divisor)) as u32;
            remainder = value % u64::from(divisor);
        }
        while self.0.last() == Some(&0) {
            self.0.pop();
        }
        remainder as u32
    }
}

impl FromStr for BigNat {
    type Err = &'static str;
    fn from_str(text: &str) -> Result<Self, Self::Err> {
        if text.is_empty() || !text.bytes().all(|ch| ch.is_ascii_digit()) {
            return Err("expected nonempty decimal Nat");
        }
        let mut result = Self::default();
        for b in text.bytes() {
            result = result.multiply_small(10).add_small(u32::from(b - b'0'));
        }
        Ok(result)
    }
}

impl fmt::Display for BigNat {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            return fmt.write_str("0");
        }
        let mut value = self.clone();
        let mut digits = Vec::new();
        while !value.is_zero() {
            digits.push((b'0' + value.div_rem_small(10) as u8) as char);
        }
        for digit in digits.into_iter().rev() {
            write!(fmt, "{digit}")?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BigInt {
    negative: bool,
    magnitude: BigNat,
}

impl BigInt {
    pub fn from_i64(value: i64) -> Self {
        Self {
            negative: value.is_negative(),
            magnitude: BigNat::from_u64(value.unsigned_abs()),
        }
    }

    pub fn add(&self, other: &Self) -> Self {
        let (negative, magnitude) = if self.negative == other.negative {
            (self.negative, self.magnitude.add(&other.magnitude))
        } else {
            match self.magnitude.cmp_magnitude(&other.magnitude) {
                Ordering::Greater => (
                    self.negative,
                    self.magnitude.sub_nonnegative(&other.magnitude),
                ),
                Ordering::Less => (
                    other.negative,
                    other.magnitude.sub_nonnegative(&self.magnitude),
                ),
                Ordering::Equal => (false, BigNat::default()),
            }
        };
        Self {
            negative: negative && !magnitude.is_zero(),
            magnitude,
        }
    }
}

impl FromStr for BigInt {
    type Err = &'static str;
    fn from_str(text: &str) -> Result<Self, Self::Err> {
        let (negative, digits) = match text.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, text.strip_prefix('+').unwrap_or(text)),
        };
        let magnitude = BigNat::from_str(digits)?;
        Ok(Self {
            negative: negative && !magnitude.is_zero(),
            magnitude,
        })
    }
}

impl fmt::Display for BigInt {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.negative {
            fmt.write_str("-")?;
        }
        write!(fmt, "{}", self.magnitude)
    }
}

/// All accepted source-level object-bearing calls are mediated by explicit
/// variants. Wrong values are caller contract violations, never coerced.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Value {
    Nat(BigNat),
    Int(BigInt),
    String(String),
    Array(Vec<Value>),
    List(Vec<Value>),
    UInt64(u64),
}

impl Value {
    pub fn nat(value: &str) -> Self {
        Self::Nat(value.parse().expect("valid decimal Nat"))
    }
    pub fn int(value: &str) -> Self {
        Self::Int(value.parse().expect("valid decimal Int"))
    }
    pub fn string(value: &str) -> Self {
        Self::String(value.to_owned())
    }
    pub fn array(values: Vec<Value>) -> Self {
        Self::Array(values)
    }
    pub fn list(values: Vec<Value>) -> Self {
        Self::List(values)
    }
    fn require_nat(&self) -> &BigNat {
        match self {
            Self::Nat(value) => value,
            _ => panic!("Lean Nat argument must be Value::Nat"),
        }
    }
    fn require_int(&self) -> &BigInt {
        match self {
            Self::Int(value) => value,
            _ => panic!("Lean Int argument must be Value::Int"),
        }
    }
    fn require_string(&self) -> &str {
        match self {
            Self::String(value) => value,
            _ => panic!("Lean String argument must be Value::String"),
        }
    }
}

pub fn nat_add(lhs: &Value, rhs: &Value) -> Value {
    Value::Nat(lhs.require_nat().add(rhs.require_nat()))
}
pub fn nat_sub(lhs: &Value, rhs: &Value) -> Value {
    Value::Nat(lhs.require_nat().sub(rhs.require_nat()))
}
pub fn nat_mul(lhs: &Value, rhs: &Value) -> Value {
    Value::Nat(lhs.require_nat().mul(rhs.require_nat()))
}
pub fn int_add(lhs: &Value, rhs: &Value) -> Value {
    Value::Int(lhs.require_int().add(rhs.require_int()))
}
pub fn string_append(lhs: &Value, rhs: &Value) -> Value {
    Value::String(format!("{}{}", lhs.require_string(), rhs.require_string()))
}
pub fn string_bytes(value: &Value) -> Value {
    Value::Nat(BigNat::from_u64(value.require_string().len() as u64))
}
pub fn string_chars(value: &Value) -> Value {
    Value::Nat(BigNat::from_u64(
        value.require_string().chars().count() as u64
    ))
}
pub fn array_push(array: &Value, element: &Value) -> Value {
    let Value::Array(values) = array else {
        panic!("Lean Array.push requires Value::Array");
    };
    let mut result = values.clone();
    result.push(element.clone());
    Value::Array(result)
}
pub fn array_size(array: &Value) -> Value {
    let Value::Array(values) = array else {
        panic!("Lean Array.size requires Value::Array");
    };
    Value::Nat(BigNat::from_u64(values.len() as u64))
}
pub fn list_reverse(list: &Value) -> Value {
    let Value::List(values) = list else {
        panic!("Lean List.reverse requires Value::List");
    };
    Value::List(values.iter().rev().cloned().collect())
}
pub fn box_uint64(value: u64) -> Value {
    Value::UInt64(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wide_unsigned_arithmetic_is_exact_and_sub_saturates() {
        let huge = BigNat::from_str("340282366920938463463374607431768211456").unwrap();
        let one = BigNat::from_u64(1);
        assert_eq!(
            huge.add(&one).to_string(),
            "340282366920938463463374607431768211457"
        );
        assert_eq!(
            huge.mul(&huge).to_string(),
            "115792089237316195423570985008687907853269984665640564039457584007913129639936"
        );
        assert_eq!(one.sub(&huge), BigNat::default());
    }

    #[test]
    fn signed_arbitrary_precision_addition() {
        let negative = BigInt::from_str("-340282366920938463463374607431768211456").unwrap();
        let positive = BigInt::from_str("340282366920938463463374607431768211455").unwrap();
        assert_eq!(negative.add(&positive).to_string(), "-1");
        assert_eq!(
            BigInt::from_i64(-1).add(&BigInt::from_i64(1)).to_string(),
            "0"
        );
    }

    #[test]
    fn utf8_counts_codepoints_not_bytes() {
        let input = Value::string("é🧮𐐷");
        assert_eq!(string_bytes(&input), Value::nat("10"));
        assert_eq!(string_chars(&input), Value::nat("3"));
    }

    #[test]
    fn arrays_are_persistent_values() {
        let original = Value::array(vec![Value::UInt64(5)]);
        let result = array_push(&original, &Value::UInt64(7));
        assert_eq!(array_size(&original), Value::nat("1"));
        assert_eq!(array_size(&result), Value::nat("2"));
    }
}
