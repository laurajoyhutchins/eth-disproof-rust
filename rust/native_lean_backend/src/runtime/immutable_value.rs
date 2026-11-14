// Original immutable Rc-backed Lean object runtime from PR #204.
// This file is embedded in generated standalone Rust, not compiled into
// the compiler plugin. Keep one canonical representation for #209/#210.

#[derive(Clone, Debug)]
pub struct __LeanValue(std::rc::Rc<__LeanValueRepr>);

#[derive(Debug)]
enum __LeanValueRepr {
    Tagged(usize),
    U8(u8), U16(u16), U32(u32), U64(u64), USize(usize),
    Ctor { tag: usize, name: &'static str, fields: Vec<__LeanValue> },
}

#[allow(dead_code)]
impl __LeanValue {
    fn tagged(v: usize) -> Self { Self(std::rc::Rc::new(__LeanValueRepr::Tagged(v))) }
    fn boxed_u8(v: u8) -> Self { Self(std::rc::Rc::new(__LeanValueRepr::U8(v))) }
    fn boxed_u16(v: u16) -> Self { Self(std::rc::Rc::new(__LeanValueRepr::U16(v))) }
    fn boxed_u32(v: u32) -> Self { Self(std::rc::Rc::new(__LeanValueRepr::U32(v))) }
    fn boxed_u64(v: u64) -> Self { Self(std::rc::Rc::new(__LeanValueRepr::U64(v))) }
    fn boxed_usize(v: usize) -> Self { Self(std::rc::Rc::new(__LeanValueRepr::USize(v))) }
    fn ctor(tag: usize, name: &'static str, fields: Vec<Self>) -> Self {
        Self(std::rc::Rc::new(__LeanValueRepr::Ctor { tag, name, fields }))
    }
    fn tag(&self) -> usize {
        match self.0.as_ref() {
            __LeanValueRepr::Tagged(v) => *v,
            __LeanValueRepr::Ctor { tag, .. } => *tag,
            _ => panic!("tried to case-analyze a boxed scalar"),
        }
    }
    fn has_ctor(&self, tag: usize, name: &str, arity: usize) -> bool {
        matches!(self.0.as_ref(), __LeanValueRepr::Ctor {tag: t, name: n, fields}
            if *t == tag && *n == name && fields.len() == arity)
    }
    fn has_tagged(&self, value: usize) -> bool {
        matches!(self.0.as_ref(), __LeanValueRepr::Tagged(v) if *v == value)
    }
    fn field(&self, index: usize) -> Self {
        match self.0.as_ref() {
            __LeanValueRepr::Ctor { fields, .. } => fields.get(index).expect("constructor field absent").clone(),
            _ => panic!("projection from a non-constructor"),
        }
    }
    fn unbox_u8(&self) -> u8 { match self.0.as_ref() {__LeanValueRepr::U8(x) => *x, _ => panic!("incorrect boxed u8") } }
    fn unbox_u16(&self) -> u16 { match self.0.as_ref() {__LeanValueRepr::U16(x) => *x, _ => panic!("incorrect boxed u16") } }
    fn unbox_u32(&self) -> u32 { match self.0.as_ref() {__LeanValueRepr::U32(x) => *x, _ => panic!("incorrect boxed u32") } }
    fn unbox_u64(&self) -> u64 { match self.0.as_ref() {__LeanValueRepr::U64(x) => *x, _ => panic!("incorrect boxed u64") } }
    fn unbox_usize(&self) -> usize { match self.0.as_ref() {__LeanValueRepr::USize(x) => *x, _ => panic!("incorrect boxed usize") } }
}
