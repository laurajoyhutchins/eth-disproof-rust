//! A source-preserving, deliberately bounded structural LaTeX -> Lean frontend.
//!
//! Independent of Leanify. It handles typed finite real vectors, matrices,
//! composition, and finite-alphabet word counts. Unsupported constructs fail;
//! no guessed quantifiers, unstated hypotheses, proof, or source rewriting.
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    pub stage: &'static str,
    pub reason: String,
}
impl Error {
    fn new(stage: &'static str, reason: impl Into<String>) -> Self {
        Self {
            stage,
            reason: reason.into(),
        }
    }
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.stage, self.reason)
    }
}
impl std::error::Error for Error {}
type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Real,
    Vector(usize),
    Matrix(usize, usize),
    Function(Box<Type>, Box<Type>),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Variable(String),
    Number(u64),
    Vector(Vec<Expr>),
    Matrix(Vec<Vec<Expr>>),
    Call(Box<Expr>, Box<Expr>),
    Compose(Box<Expr>, Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Pow(Box<Expr>, u64),
    Identity(usize),
}
#[derive(Debug, Clone)]
pub enum Def {
    VectorMap {
        name: String,
        input_dim: usize,
        output_dim: usize,
        params: Vec<String>,
        body: Expr,
    },
    Matrix {
        name: String,
        rows: Vec<Vec<Expr>>,
    },
}
#[derive(Debug, Clone)]
pub enum Quantifier {
    Real(Vec<String>),
    Vector(String, usize),
    None,
}
#[derive(Debug, Clone)]
pub enum Claim {
    Equality {
        quant: Quantifier,
        lhs: Expr,
        rhs: Expr,
    },
    WordCount {
        base: usize,
        length: usize,
        count: usize,
    },
}
#[derive(Debug, Clone)]
pub struct Article {
    pub definitions: Vec<Def>,
    pub claim: Claim,
}

fn bad(stage: &'static str, msg: impl Into<String>) -> Error {
    Error::new(stage, msg)
}
fn checked_dim(n: usize) -> Result<usize> {
    if n == 0 || n > 32 {
        Err(bad(
            "types",
            format!("dimension {n} outside supported range 1..=32"),
        ))
    } else {
        Ok(n)
    }
}
fn identifier(s: &str) -> Result<String> {
    if !s.is_empty()
        && s.len() <= 64
        && s.as_bytes()[0].is_ascii_alphabetic()
        && s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
    {
        Ok(s.to_owned())
    } else {
        Err(bad("identifier", format!("invalid symbol {s:?}")))
    }
}

// Scans inline `$...$`, rejecting unclosed delimiters. Math displays are not
// silently treated as plain English. Escaped `\$` is not a math delimiter.
fn math_spans(source: &str) -> Result<Vec<(usize, usize, String)>> {
    let bytes = source.as_bytes();
    let mut spans = Vec::new();
    let mut start = None;
    for i in 0..bytes.len() {
        if bytes[i] == b'$' && (i == 0 || bytes[i - 1] != b'\\') {
            if let Some(s) = start.take() {
                spans.push((s - 1, i + 1, source[s..i].to_owned()))
            } else {
                start = Some(i + 1)
            }
        }
    }
    if start.is_some() {
        return Err(bad("tex", "unterminated inline math"));
    }
    Ok(spans)
}
fn split_words(s: &str) -> Vec<&str> {
    s.split_whitespace().filter(|x| !x.is_empty()).collect()
}
fn parse_named_number(s: &str) -> Option<usize> {
    match s.trim().to_lowercase().as_str() {
        "zero" => Some(0),
        "one" => Some(1),
        "two" => Some(2),
        "three" => Some(3),
        "four" => Some(4),
        "five" => Some(5),
        "six" => Some(6),
        "seven" => Some(7),
        "eight" => Some(8),
        "nine" => Some(9),
        "ten" => Some(10),
        "eleven" => Some(11),
        "twelve" => Some(12),
        "thirteen" => Some(13),
        "fourteen" => Some(14),
        "fifteen" => Some(15),
        "sixteen" => Some(16),
        other => other.parse::<usize>().ok(),
    }
}
fn words_count(text: &str) -> Result<Claim> {
    // A grammatical rule, not a hard-coded result: finite-alphabet words are
    // functions Fin(length) -> Fin(alphabet size).
    let normalized = text.split_whitespace().collect::<Vec<_>>().join(" ");
    let words = split_words(normalized.trim_end_matches('.'));
    if words.len() < 11
        || words[..4] != ["The", "set", "of", "binary"]
            && words.get(0..3) != Some(&["The", "set", "of"][..])
    {
        return Err(bad("prose", "unsupported cardinality statement"));
    }
    let p = words
        .iter()
        .position(|x| *x == "words")
        .ok_or_else(|| bad("prose", "no word family"))?;
    if p < 3 || words.get(p + 1) != Some(&"of") || words.get(p + 2) != Some(&"length") {
        return Err(bad("prose", "expected 'words of length N'"));
    }
    let base = match words[p - 1] {
        "binary" => 2,
        "ternary" => 3,
        "quaternary" => 4,
        x => {
            if let Some(num) = x.strip_prefix("base-") {
                parse_named_number(num).ok_or_else(|| bad("prose", "unknown alphabet size"))?
            } else {
                return Err(bad("prose", format!("unknown alphabet {x:?}")));
            }
        }
    };
    let length = parse_named_number(words.get(p + 3).copied().unwrap_or(""))
        .ok_or_else(|| bad("prose", "unknown word length"))?;
    let count = match words.get(p + 4..) {
        Some(["has", n, "elements"]) => {
            parse_named_number(n).ok_or_else(|| bad("prose", "unknown cardinal"))?
        }
        _ => return Err(bad("prose", "expected 'has N elements'")),
    };
    checked_dim(length)?;
    checked_dim(base)?;
    Ok(Claim::WordCount {
        base,
        length,
        count,
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Ident(String),
    Num(u64),
    Lp,
    Rp,
    Comma,
    Plus,
    Minus,
    Star,
    Caret,
    Eq,
    Compose,
    Colon,
    Arrow,
    Assign,
    Membership,
    Matrix(Vec<Vec<Token>>),
}
// TeX math lexing. Matrix cells are recursively lexed as expressions, preserving
// source-order and requiring identical row widths.
fn lex_math(raw: &str) -> Result<Vec<Token>> {
    let text = raw.trim();
    let mut out = Vec::new();
    let mut i = 0;
    while i < text.len() {
        let c = text.as_bytes()[i];
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if text[i..].starts_with("\\begin{pmatrix}") {
            let off = "\\begin{pmatrix}".len();
            let term = "\\end{pmatrix}";
            let tail = &text[i + off..];
            let end = tail
                .find(term)
                .ok_or_else(|| bad("math", "unclosed pmatrix"))?;
            let body = &tail[..end];
            let mut rows = Vec::new();
            for row in body.split("\\\\") {
                let mut cells = Vec::new();
                for cell in row.split('&') {
                    let tokens = lex_math(cell)?;
                    if tokens.is_empty() {
                        return Err(bad("math", "empty matrix cell"));
                    }
                    cells.push(tokens);
                }
                if cells.is_empty() {
                    return Err(bad("math", "empty matrix row"));
                }
                rows.push(cells);
            }
            if rows.is_empty() || rows.iter().any(|r| r.len() != rows[0].len()) {
                return Err(bad("math", "ragged matrix"));
            }
            // Store cells as a matrix of parenthesized token streams; parsing
            // them individually avoids misreading delimiters as arithmetic.
            let mut data = Vec::new();
            for row in rows {
                data.push(row.into_iter().map(|x| Token::Matrix(vec![x])).collect());
            }
            out.push(Token::Matrix(data));
            i += off + end + term.len();
            continue;
        }
        if c == b'\\' {
            let suffix = &text[i..];
            let macros = [
                ("\\mathbb{R}", "R"),
                ("\\mathbb{N}", "N"),
                ("\\coloneqq", ":="),
                ("\\circ", "circ"),
                ("\\to", "to"),
                ("\\in", "in"),
                ("\\cdot", "*"),
                ("\\times", "times"),
            ];
            if let Some((macro_name, kind)) = macros.iter().find(|(s, _)| suffix.starts_with(s)) {
                match *kind {
                    "R" => out.push(Token::Ident("R".into())),
                    "N" => out.push(Token::Ident("N".into())),
                    ":=" => out.push(Token::Assign),
                    "circ" => out.push(Token::Compose),
                    "to" => out.push(Token::Arrow),
                    "in" => out.push(Token::Membership),
                    "*" => out.push(Token::Star),
                    _ => return Err(bad("math", "unsupported command")),
                }
                i += macro_name.len();
                continue;
            }
            return Err(bad(
                "math",
                format!(
                    "unsupported TeX macro at {:?}",
                    suffix.chars().take(20).collect::<String>()
                ),
            ));
        }
        let tok = match c {
            b'(' => Token::Lp,
            b')' => Token::Rp,
            b',' => Token::Comma,
            b'+' => Token::Plus,
            b'-' => Token::Minus,
            b'*' => Token::Star,
            b'^' => Token::Caret,
            b'=' => Token::Eq,
            b':' => Token::Colon,
            b'0'..=b'9' => {
                let begin = i;
                while i < text.len() && text.as_bytes()[i].is_ascii_digit() {
                    i += 1;
                }
                let v = text[begin..i]
                    .parse()
                    .map_err(|_| bad("math", "numeric overflow"))?;
                out.push(Token::Num(v));
                continue;
            }
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => {
                let begin = i;
                while i < text.len()
                    && (text.as_bytes()[i].is_ascii_alphanumeric() || text.as_bytes()[i] == b'_')
                {
                    i += 1;
                }
                out.push(Token::Ident(text[begin..i].to_owned()));
                continue;
            }
            _ => {
                return Err(bad(
                    "math",
                    format!("unrecognized math character {:?}", text[i..].chars().next()),
                ))
            }
        };
        out.push(tok);
        i += 1;
    }
    Ok(out)
}
#[derive(Debug)]
struct Parser {
    tokens: Vec<Token>,
    index: usize,
}
impl Parser {
    fn new(t: Vec<Token>) -> Self {
        Self {
            tokens: t,
            index: 0,
        }
    }
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.index)
    }
    fn eat(&mut self, x: &Token) -> bool {
        if self.peek() == Some(x) {
            self.index += 1;
            true
        } else {
            false
        }
    }
    fn next(&mut self) -> Result<Token> {
        let t = self
            .peek()
            .cloned()
            .ok_or_else(|| bad("math", "unexpected end"))?;
        self.index += 1;
        Ok(t)
    }
    fn expect(&mut self, t: Token) -> Result<()> {
        if self.eat(&t) {
            Ok(())
        } else {
            Err(bad(
                "math",
                format!("expected {t:?}, got {:?}", self.peek()),
            ))
        }
    }
    fn eof(&self) -> Result<()> {
        if self.peek().is_some() {
            Err(bad(
                "math",
                format!("unconsumed tokens: {:?}", &self.tokens[self.index..]),
            ))
        } else {
            Ok(())
        }
    }
    fn atom(&mut self) -> Result<Expr> {
        match self.next()? {
            Token::Num(n) => Ok(Expr::Number(n)),
            Token::Ident(s) => {
                if let Some(n) = s.strip_prefix("I_").and_then(|x| x.parse::<usize>().ok()) {
                    checked_dim(n)?;
                    Ok(Expr::Identity(n))
                } else {
                    Ok(Expr::Variable(identifier(&s)?))
                }
            }
            Token::Minus => Ok(Expr::Sub(
                Box::new(Expr::Number(0)),
                Box::new(self.expression(8)?),
            )),
            Token::Lp => {
                let a = self.expression(0)?;
                if self.eat(&Token::Comma) {
                    let mut es = vec![a];
                    loop {
                        es.push(self.expression(0)?);
                        if !self.eat(&Token::Comma) {
                            break;
                        }
                    }
                    self.expect(Token::Rp)?;
                    Ok(Expr::Vector(es))
                } else {
                    self.expect(Token::Rp)?;
                    Ok(a)
                }
            }
            Token::Matrix(data) => {
                let mut rows = Vec::new();
                for row in data {
                    let mut cells = Vec::new();
                    for cell in row {
                        match cell {
                            Token::Matrix(one) if one.len() == 1 => {
                                let mut p = Parser::new(one[0].clone());
                                let v = p.expression(0)?;
                                p.eof()?;
                                cells.push(v)
                            }
                            _ => return Err(bad("math", "invalid matrix cell")),
                        }
                    }
                    rows.push(cells);
                }
                Ok(Expr::Matrix(rows))
            }
            t => Err(bad("math", format!("unexpected atom {t:?}"))),
        }
    }
    fn expression(&mut self, min_prec: u8) -> Result<Expr> {
        let mut left = self.atom()?;
        loop {
            if self.peek() == Some(&Token::Lp) && 9 >= min_prec {
                self.next()?;
                let mut args = Vec::new();
                if !self.eat(&Token::Rp) {
                    loop {
                        args.push(self.expression(0)?);
                        if self.eat(&Token::Rp) {
                            break;
                        }
                        self.expect(Token::Comma)?;
                    }
                }
                if args.is_empty() {
                    return Err(bad("math", "zero-argument function application"));
                }
                let arg = if args.len() == 1 {
                    args.remove(0)
                } else {
                    Expr::Vector(args)
                };
                left = Expr::Call(Box::new(left), Box::new(arg));
                continue;
            }
            let Some(op) = self.peek().cloned() else {
                break;
            };
            let (prec, right_associative) = match op {
                Token::Eq => (1, false),
                Token::Compose => (2, true),
                Token::Plus | Token::Minus => (3, false),
                Token::Star => (4, false),
                Token::Caret => (8, true),
                _ => break,
            };
            if prec < min_prec {
                break;
            }
            self.next()?;
            if op == Token::Caret {
                let n = match self.next()? {
                    Token::Num(n) => n,
                    t => {
                        return Err(bad(
                            "math",
                            format!("power exponent must be literal Nat, found {t:?}"),
                        ))
                    }
                };
                if n > 32 {
                    return Err(bad("math", "exponent > 32 exceeds resource cap"));
                }
                left = Expr::Pow(Box::new(left), n);
                continue;
            }
            let right = self.expression(prec + u8::from(!right_associative))?;
            left = match op {
                Token::Eq => return Err(bad("math", "equality allowed only at theorem top level")),
                Token::Compose => Expr::Compose(Box::new(left), Box::new(right)),
                Token::Plus => Expr::Add(Box::new(left), Box::new(right)),
                Token::Minus => Expr::Sub(Box::new(left), Box::new(right)),
                Token::Star => Expr::Mul(Box::new(left), Box::new(right)),
                _ => unreachable!(),
            };
        }
        Ok(left)
    }
}
fn parse_equality(s: &str) -> Result<(Expr, Expr)> {
    let toks = lex_math(s)?;
    let idx = toks
        .iter()
        .position(|t| *t == Token::Eq)
        .ok_or_else(|| bad("theorem", "equality missing"))?;
    if toks[idx + 1..].contains(&Token::Eq) {
        return Err(bad("theorem", "chained equality unsupported"));
    }
    Ok((
        parse_from_tokens(toks[..idx].to_vec())?,
        parse_from_tokens(toks[idx + 1..].to_vec())?,
    ))
}
fn parse_from_tokens(toks: Vec<Token>) -> Result<Expr> {
    let mut p = Parser::new(toks);
    let e = p.expression(0)?;
    p.eof()?;
    Ok(e)
}
fn parse_definition(signature: &str, body: &str) -> Result<Def> {
    let toks = lex_math(signature)?;
    let mut p = Parser::new(toks);
    let name = match p.next()? {
        Token::Ident(s) => identifier(&s)?,
        _ => return Err(bad("define", "function name missing")),
    };
    p.expect(Token::Colon)?;
    match p.next()? {
        Token::Ident(s) if s == "R" => (),
        t => {
            return Err(bad(
                "define",
                format!("expected real vector domain, found {t:?}"),
            ))
        }
    };
    p.expect(Token::Caret)?;
    let n = match p.next()? {
        Token::Num(n) => checked_dim(n as usize)?,
        _ => return Err(bad("define", "vector dimension missing")),
    };
    p.expect(Token::Arrow)?;
    p.expect(Token::Ident("R".into()))?;
    p.expect(Token::Caret)?;
    let m = match p.next()? {
        Token::Num(n) => checked_dim(n as usize)?,
        _ => return Err(bad("define", "vector codomain missing")),
    };
    p.eof()?;
    let t = lex_math(body)?;
    let mut a = Parser::new(t);
    a.expect(Token::Ident(name.clone()))?;
    a.expect(Token::Lp)?;
    let mut params = Vec::new();
    loop {
        match a.next()? {
            Token::Ident(x) => params.push(identifier(&x)?),
            t => {
                return Err(bad(
                    "define",
                    format!("expected formal variable, found {t:?}"),
                ))
            }
        }
        if a.eat(&Token::Rp) {
            break;
        }
        a.expect(Token::Comma)?;
    }
    if params.len() != n || params.iter().collect::<BTreeSet<_>>().len() != n {
        return Err(bad(
            "define",
            format!(
                "arity {} differs from dimension {n} or variables repeat",
                params.len()
            ),
        ));
    }
    a.expect(Token::Assign)?;
    let rhs = a.expression(0)?;
    a.eof()?;
    let expected = BTreeMap::from_iter(params.iter().map(|p| (p.clone(), Type::Real)));
    if infer(&rhs, &expected)? != Type::Vector(m) {
        return Err(bad("define", "vector output has wrong type"));
    }
    Ok(Def::VectorMap {
        name,
        input_dim: n,
        output_dim: m,
        params,
        body: rhs,
    })
}
fn parse_matrix_definition(text: &str) -> Result<Def> {
    let toks = lex_math(text)?;
    let i = toks
        .iter()
        .position(|t| *t == Token::Eq)
        .ok_or_else(|| bad("define", "expected matrix equality"))?;
    let name = match toks.as_slice() {
        [Token::Ident(x), Token::Eq, ..] => identifier(x)?,
        _ => return Err(bad("define", "expected 'Let $P = matrix$'")),
    };
    if i != 1 {
        return Err(bad("define", "matrix LHS must be a symbol"));
    }
    let matrix = parse_from_tokens(toks[i + 1..].to_vec())?;
    let Expr::Matrix(rows) = matrix else {
        return Err(bad("define", "matrix RHS expected"));
    };
    let env = BTreeMap::new();
    if !matches!(
        infer(&Expr::Matrix(rows.clone()), &env)?,
        Type::Matrix(_, _)
    ) {
        return Err(bad("define", "invalid matrix definition"));
    }
    Ok(Def::Matrix { name, rows })
}
fn parse_theorem(body: &str) -> Result<Claim> {
    let text = body.trim();
    let spans = math_spans(text)?;
    if text.starts_with("The set of ") {
        if !spans.is_empty() {
            return Err(bad("prose", "mixed formula/text cardinality unsupported"));
        }
        return words_count(text);
    }
    if text.starts_with("For all real numbers ") {
        if spans.len() != 2 {
            return Err(bad("theorem", "expected one binder and one formula"));
        }
        let names = spans[0]
            .2
            .split(',')
            .map(|x| identifier(x.trim()))
            .collect::<Result<Vec<_>>>()?;
        if names.is_empty() || names.iter().collect::<BTreeSet<_>>().len() != names.len() {
            return Err(bad("theorem", "invalid binder"));
        }
        let before = &text["For all real numbers ".len()..spans[0].0];
        let between = &text[spans[0].1..spans[1].0];
        let after = &text[spans[1].1..];
        if !before.trim().is_empty() || between.trim() != "," || after.trim() != "." {
            return Err(bad("theorem", "unrecognized theorem prose"));
        }
        let (lhs, rhs) = parse_equality(&spans[1].2)?;
        Ok(Claim::Equality {
            quant: Quantifier::Real(names),
            lhs,
            rhs,
        })
    } else if text.starts_with("For every ") {
        if spans.len() != 2 {
            return Err(bad("theorem", "expected vector binder and formula"));
        }
        let mut toks = lex_math(&spans[0].2)?;
        let name = match toks.first() {
            Some(Token::Ident(s)) => identifier(s)?,
            _ => return Err(bad("theorem", "invalid bound vector")),
        };
        if toks.len() != 5 || toks[1] != Token::Membership {
            // A unicode/TeX membership macro is handled by prepass below.
            return Err(bad(
                "theorem",
                format!("unsupported vector binder: {:?}", toks),
            ));
        }
        toks.drain(..2);
        let n = match toks.as_slice() {
            [Token::Ident(x), Token::Caret, Token::Num(n)] if x == "R" => checked_dim(*n as usize)?,
            _ => return Err(bad("theorem", "bad vector dimension")),
        };
        let between = &text[spans[0].1..spans[1].0];
        if between.trim() != "," || text[spans[1].1..].trim() != "." {
            return Err(bad("theorem", "unrecognized vector quantifier prose"));
        }
        let (lhs, rhs) = parse_equality(&spans[1].2)?;
        Ok(Claim::Equality {
            quant: Quantifier::Vector(name, n),
            lhs,
            rhs,
        })
    } else if spans.len() == 1
        && text[..spans[0].0].trim().is_empty()
        && text[spans[0].1..].trim() == "."
    {
        let (lhs, rhs) = parse_equality(&spans[0].2)?;
        Ok(Claim::Equality {
            quant: Quantifier::None,
            lhs,
            rhs,
        })
    } else {
        Err(bad(
            "theorem",
            "unsupported sentence form; refusing to guess quantifiers",
        ))
    }
}
fn normalize_comments(source: &str) -> String {
    // Drop TeX comments outside \verb and escaped \%; this grammar supports no \verb.
    source
        .lines()
        .map(|line| {
            let mut cut = line.len();
            for (i, c) in line.char_indices() {
                if c == '%' && (i == 0 || !line[..i].ends_with('\\')) {
                    cut = i;
                    break;
                }
            }
            line[..cut].to_string()
        })
        .collect::<Vec<_>>()
        .join("\n")
}
fn remove_label(s: &str) -> String {
    let mut out = s.to_owned();
    while let Some(i) = out.find("\\label{") {
        let j = i + "\\label{".len();
        if let Some(k) = out[j..].find('}') {
            out.replace_range(i..j + k + 1, "");
        } else {
            break;
        }
    }
    out
}
pub fn parse_article(raw: &str) -> Result<Article> {
    if raw.len() > 1_000_000 {
        return Err(bad("tex", "source exceeds 1 MiB cap"));
    }
    let source = normalize_comments(raw);
    if [
        "\\input{",
        "\\include{",
        "\\subfile{",
        "\\def\\",
        "\\newcommand",
        "\\renewcommand",
        "\\catcode",
        "\\write18",
    ]
    .iter()
    .any(|s| source.contains(s))
    {
        return Err(bad(
            "tex",
            "external inputs or macro rewriting require explicit expansion and source provenance",
        ));
    }
    let begin = "\\begin{theorem}";
    let end = "\\end{theorem}";
    let i = source
        .find(begin)
        .ok_or_else(|| bad("tex", "missing theorem environment"))?;
    let after = &source[i + begin.len()..];
    let j = after
        .find(end)
        .ok_or_else(|| bad("tex", "unclosed theorem"))?;
    if source.matches(begin).count() != 1 || source.matches(end).count() != 1 {
        return Err(bad("tex", "expected exactly one theorem"));
    }
    let preamble = &source[..i];
    let theorem = &after[..j];
    let spans = math_spans(preamble)?;
    let mut defs = Vec::new();
    let mut seen = BTreeSet::new();
    // Definition detection is paragraph-local and requires literal 'Define ... by ...'.
    // We do not treat arbitrary prose as a definition.
    for window in spans.windows(2) {
        let lhs = &window[0];
        let rhs = &window[1];
        let before = &preamble[..lhs.0];
        let text_before = before.rsplit(['\n', '.']).next().unwrap_or("").trim();
        let between = preamble[lhs.1..rhs.0].trim();
        if text_before == "Define" && between == "by" {
            let d = parse_definition(&lhs.2, &rhs.2)?;
            let n = match &d {
                Def::VectorMap { name, .. } | Def::Matrix { name, .. } => name.clone(),
            };
            if !seen.insert(n.clone()) {
                return Err(bad("define", format!("duplicate definition {n}")));
            }
            defs.push(d);
        }
    }
    for span in &spans {
        let before = &preamble[..span.0];
        let text_before = before.rsplit(['\n', '.']).next().unwrap_or("").trim();
        if text_before == "Let" {
            let d = parse_matrix_definition(&span.2)?;
            let n = match &d {
                Def::Matrix { name, .. } | Def::VectorMap { name, .. } => name.clone(),
            };
            if !seen.insert(n.clone()) {
                return Err(bad("define", format!("duplicate definition {n}")));
            }
            defs.push(d);
        }
    }
    // A source definition that fails to parse must not silently disappear.
    if preamble.matches("Define $").count()
        != defs
            .iter()
            .filter(|d| matches!(d, Def::VectorMap { .. }))
            .count()
        || preamble.matches("Let $").count()
            != defs
                .iter()
                .filter(|d| matches!(d, Def::Matrix { .. }))
                .count()
    {
        return Err(bad(
            "define",
            "one or more source definitions were not parsed",
        ));
    }
    let claim = parse_theorem(&remove_label(theorem))?;
    let mut env = BTreeMap::new();
    for d in &defs {
        match d {
            Def::VectorMap {
                name,
                input_dim,
                output_dim,
                ..
            } => {
                env.insert(
                    name.clone(),
                    Type::Function(
                        Box::new(Type::Vector(*input_dim)),
                        Box::new(Type::Vector(*output_dim)),
                    ),
                );
            }
            Def::Matrix { name, rows } => {
                env.insert(name.clone(), Type::Matrix(rows.len(), rows[0].len()));
            }
        }
    }
    if let Claim::Equality { quant, lhs, rhs } = &claim {
        match quant {
            Quantifier::Real(names) => {
                for name in names {
                    if env.insert(name.clone(), Type::Real).is_some() {
                        return Err(bad("theorem", "binder shadows definition"));
                    }
                }
            }
            Quantifier::Vector(name, dim) => {
                if env.insert(name.clone(), Type::Vector(*dim)).is_some() {
                    return Err(bad("theorem", "binder shadows definition"));
                }
            }
            Quantifier::None => {}
        }
        let lt = infer(lhs, &env)?;
        let rt = infer(rhs, &env)?;
        if lt != rt {
            return Err(bad(
                "types",
                format!("equality has incompatible sides {lt:?} and {rt:?}"),
            ));
        }
    }
    Ok(Article {
        definitions: defs,
        claim,
    })
}
fn infer(e: &Expr, env: &BTreeMap<String, Type>) -> Result<Type> {
    Ok(match e {
        Expr::Variable(x) => env
            .get(x)
            .cloned()
            .ok_or_else(|| bad("types", format!("undefined symbol {x}")))?,
        Expr::Number(_) => Type::Real,
        Expr::Vector(xs) => {
            checked_dim(xs.len())?;
            for x in xs {
                if infer(x, env)? != Type::Real {
                    return Err(bad("types", "non-real vector coordinate"));
                }
            }
            Type::Vector(xs.len())
        }
        Expr::Matrix(rows) => {
            checked_dim(rows.len())?;
            checked_dim(rows[0].len())?;
            if rows.iter().any(|r| r.len() != rows[0].len()) {
                return Err(bad("types", "ragged matrix"));
            }
            for row in rows {
                for x in row {
                    if infer(x, env)? != Type::Real {
                        return Err(bad("types", "non-real matrix cell"));
                    }
                }
            }
            Type::Matrix(rows.len(), rows[0].len())
        }
        Expr::Call(f, arg) => {
            let ft = infer(f, env)?;
            let at = infer(arg, env)?;
            match ft {
                Type::Function(input, output) if *input == at => *output,
                _ => {
                    return Err(bad(
                        "types",
                        format!("function application has incompatible argument type {at:?}"),
                    ))
                }
            }
        }
        Expr::Compose(f, g) => {
            let ft = infer(f, env)?;
            let gt = infer(g, env)?;
            match (ft, gt) {
                (Type::Function(a, b), Type::Function(c, d)) if *a == *d => Type::Function(c, b),
                _ => return Err(bad("types", "function composition types mismatch")),
            }
        }
        Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) => {
            if infer(a, env)? != Type::Real || infer(b, env)? != Type::Real {
                return Err(bad("types", "scalar arithmetic on non-reals"));
            }
            Type::Real
        }
        Expr::Pow(base, _) => match infer(base, env)? {
            Type::Real => Type::Real,
            Type::Matrix(a, b) if a == b => Type::Matrix(a, b),
            _ => {
                return Err(bad(
                    "types",
                    "power of nonsquare matrix or unsupported type",
                ))
            }
        },
        Expr::Identity(n) => Type::Matrix(*n, *n),
    })
}
fn render_expr(expr: &Expr, local: &BTreeMap<String, String>) -> Result<String> {
    Ok(match expr {
        Expr::Variable(x) => local.get(x).cloned().unwrap_or_else(|| x.clone()),
        Expr::Number(n) => n.to_string(),
        Expr::Vector(xs) => format!(
            "![{}]",
            xs.iter()
                .map(|x| render_expr(x, local))
                .collect::<Result<Vec<_>>>()?
                .join(", ")
        ),
        Expr::Matrix(rows) => format!(
            "!![{}]",
            rows.iter()
                .map(|r| r
                    .iter()
                    .map(|x| render_expr(x, local))
                    .collect::<Result<Vec<_>>>()
                    .map(|v| v.join(", ")))
                .collect::<Result<Vec<_>>>()?
                .join("; ")
        ),
        Expr::Call(f, arg) => format!("({} {})", render_expr(f, local)?, render_expr(arg, local)?),
        Expr::Compose(f, g) => format!(
            "(fun v => {} ({} v))",
            render_expr(f, local)?,
            render_expr(g, local)?
        ),
        Expr::Add(a, b) => format!("({} + {})", render_expr(a, local)?, render_expr(b, local)?),
        Expr::Sub(a, b) => format!("({} - {})", render_expr(a, local)?, render_expr(b, local)?),
        Expr::Mul(a, b) => format!("({} * {})", render_expr(a, local)?, render_expr(b, local)?),
        Expr::Pow(base, n) => format!("({} ^ {n})", render_expr(base, local)?),
        Expr::Identity(n) => format!("(1 : Matrix (Fin {n}) (Fin {n}) ℝ)"),
    })
}
fn render_def(def: &Def) -> Result<String> {
    Ok(match def {
        Def::VectorMap {
            name,
            input_dim,
            output_dim,
            params,
            body,
        } => {
            let local = BTreeMap::from_iter(
                params
                    .iter()
                    .enumerate()
                    .map(|(i, x)| (x.clone(), format!("v ⟨{i}, by decide⟩"))),
            );
            // Every input component gets an index with a kernel-verified bound.
            format!(
                "def {name} (v : Fin {input_dim} → ℝ) : Fin {output_dim} → ℝ := {}\n",
                render_expr(body, &local)?
            )
        }
        Def::Matrix { name, rows } => {
            let n = rows.len();
            let m = rows[0].len();
            format!(
                "def {name} : Matrix (Fin {n}) (Fin {m}) ℝ := {}\n",
                render_expr(&Expr::Matrix(rows.clone()), &BTreeMap::new())?
            )
        }
    })
}
pub fn to_lean(article: &Article, namespace: &str) -> Result<String> {
    let name = identifier(namespace)?;
    let mut lines = vec![
        "import Mathlib".to_string(),
        "open scoped Matrix".to_string(),
        format!("namespace {name}"),
        String::new(),
    ];
    for d in &article.definitions {
        lines.push(render_def(d)?);
    }
    let prop = match &article.claim {
        Claim::WordCount {
            base,
            length,
            count,
        } => format!("(Fintype.card (Fin {length} → Fin {base}) = {count})"),
        Claim::Equality { quant, lhs, rhs } => {
            let binds = match quant {
                Quantifier::None => String::new(),
                Quantifier::Real(names) => format!("∀ ({} : ℝ), ", names.join(" ")),
                Quantifier::Vector(x, n) => format!("∀ ({x} : Fin {n} → ℝ), "),
            };
            format!(
                "{}({} = {})",
                binds,
                render_expr(lhs, &BTreeMap::new())?,
                render_expr(rhs, &BTreeMap::new())?
            )
        }
    };
    lines.push(format!("def claim : Prop := {prop}"));
    lines.push(format!("end {name}"));
    lines.push(String::new());
    Ok(lines.join("\n"))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn article(defs: &str, stmt: &str) -> String {
        format!("\\documentclass{{article}}\n\\begin{{document}}\n{defs}\n\\begin{{theorem}}\\label{{x}}\n{stmt}\n\\end{{theorem}}\n\\end{{document}}\n")
    }
    #[test]
    fn matrix_three_by_three_holdout() {
        let src = article(
            r"Let $A=\begin{pmatrix}1&0&0\\0&1&0\\0&0&1\end{pmatrix}$.",
            r"$A^3=I_3$.",
        );
        let lean = to_lean(&parse_article(&src).unwrap(), "Sample").unwrap();
        assert!(lean.contains("Matrix (Fin 3) (Fin 3) ℝ"));
        assert!(lean.contains("!![1, 0, 0; 0, 1, 0; 0, 0, 1]"));
    }
    #[test]
    fn base_three_length_four_holdout() {
        let src = article(
            "",
            "The set of ternary words of length four has eighty-one elements.",
        );
        assert!(parse_article(&src).is_err());
        let src = article("", "The set of ternary words of length 4 has 81 elements.");
        assert!(to_lean(&parse_article(&src).unwrap(), "T")
            .unwrap()
            .contains("Fin 4 → Fin 3"));
    }
    #[test]
    fn false_cardinality_remains_false() {
        let src = article("", "The set of binary words of length 3 has 9 elements.");
        let out = to_lean(&parse_article(&src).unwrap(), "Test").unwrap();
        assert!(out.contains("= 9"));
        assert!(!out.contains("= 8"));
    }
    #[test]
    fn unbound_symbol_rejected() {
        assert!(parse_article(&article("", r"$Z^2=I_2$.")).is_err());
    }
    #[test]
    fn dimension_mismatch_rejected() {
        let source = article(
            r"Define $f:\mathbb{R}^3\to\mathbb{R}^3$ by $f(x,y,z)\coloneqq(y,x)$.",
            r"For all real numbers $x,y,z$, $f(x,y,z)=(x,y,z)$.",
        );
        assert!(parse_article(&source).is_err());
    }
    #[test]
    fn different_dimensions_are_typable() {
        let src = article(
            r"Define $f:\mathbb{R}^3\to\mathbb{R}^2$ by $f(x,y,z)\coloneqq(y,x)$.",
            r"For all real numbers $x,y,z$, $f(x,y,z)=(y,x)$.",
        );
        let out = to_lean(&parse_article(&src).unwrap(), "Dims").unwrap();
        assert!(out.contains("Fin 3 → ℝ) : Fin 2 → ℝ"));
    }
    #[test]
    fn vector_dimension_five_not_special_cased() {
        let src = article(
            r"Define $s:\mathbb{R}^5\to\mathbb{R}^5$ by $s(a,b,c,d,e)\coloneqq(e,d,c,b,a)$.",
            r"For all real numbers $a,b,c,d,e$, $s(s(a,b,c,d,e))=(a,b,c,d,e)$.",
        );
        assert!(to_lean(&parse_article(&src).unwrap(), "Five")
            .unwrap()
            .contains("Fin 5 → ℝ"));
    }
    #[test]
    fn type_rejects_illegal_composition() {
        let src = article(
            r"Define $f:\mathbb{R}^3\to\mathbb{R}^2$ by $f(x,y,z)\coloneqq(y,x)$.",
            r"For all real numbers $x,y,z$, $f(f(x,y,z))=(y,x)$.",
        );
        assert!(parse_article(&src).is_err());
    }
    #[test]
    fn matrix_size_and_identity_must_agree() {
        let src = article(
            r"Let $P=\begin{pmatrix}0&1\\1&0\end{pmatrix}$.",
            r"$P^2=I_3$.",
        );
        assert!(parse_article(&src).is_err());
    }
    #[test]
    fn false_involution_is_preserved() {
        let src = article(
            r"Define $s:\mathbb{R}^2\to\mathbb{R}^2$ by $s(x,y)\coloneqq(y,x)$.",
            r"For all real numbers $x,y$, $s(s(x,y))=(y,x)$.",
        );
        let out = to_lean(&parse_article(&src).unwrap(), "Wrong").unwrap();
        assert!(out.contains("= ![y, x]"));
    }
    #[test]
    fn source_includes_must_be_explicitly_rejected() {
        let src = article(r"\input{hidden.tex}", r"$3=3$.");
        assert!(parse_article(&src).is_err());
    }
    #[test]
    fn very_large_dimensions_rejected() {
        let src = article(
            r"Define $f:\mathbb{R}^100\to\mathbb{R}^100$ by $f(x)\coloneqq(x)$.",
            r"$3=3$.",
        );
        assert!(parse_article(&src).is_err());
    }
    #[test]
    fn dimension_sweep_is_not_fixture_specific() {
        let alphabet = "abcdefghijklmnopqrstuvwxyz".chars().collect::<Vec<_>>();
        for n in 2..=16 {
            let names = alphabet[..n]
                .iter()
                .map(char::to_string)
                .collect::<Vec<_>>();
            let rev = names.iter().rev().cloned().collect::<Vec<_>>();
            let def = format!(
                r"Define $r:\mathbb{{R}}^{n}\to\mathbb{{R}}^{n}$ by $r({})\coloneqq({})$.",
                names.join(","),
                rev.join(",")
            );
            let claim = format!(
                "For all real numbers ${}$, $r(r({}))=({})$.",
                names.join(","),
                names.join(","),
                names.join(",")
            );
            let output = to_lean(&parse_article(&article(&def, &claim)).unwrap(), "Sweep").unwrap();
            assert!(output.contains(&format!("Fin {n} → ℝ")));
        }
    }
    #[test]
    fn finite_word_count_sweep_preserves_false_values() {
        for base in 2..=8 {
            for length in 1..=10 {
                let statement =
                    format!("The set of base-{base} words of length {length} has 7 elements.");
                let generated =
                    to_lean(&parse_article(&article("", &statement)).unwrap(), "Words").unwrap();
                assert!(generated.contains(&format!("Fin {length} → Fin {base}")));
                assert!(generated.contains("= 7"));
            }
        }
    }
    #[test]
    fn unsupported_latex_never_introduces_assumptions() {
        for fragment in [
            r"\input{hidden.tex}",
            r"\newcommand{\thing}{0}",
            r"\include{chapter}",
        ] {
            assert!(parse_article(&article(fragment, r"$2=2$.")).is_err());
        }
    }
    #[test]
    fn unused_definition_does_not_disappear() {
        let source = article(
            r"Define $g:\mathbb{R}^2\to\mathbb{R}^2$ by $g(x,y)\coloneqq(y,x)$.",
            r"$3=3$.",
        );
        let out = to_lean(&parse_article(&source).unwrap(), "Q").unwrap();
        assert!(out.contains("def g"));
    }
}
