#![feature(exclusive_range_pattern)]

use std::collections::HashMap;

pub enum Value {
    Rat(i64, i64),
    Int(i64),
    Float(f64),
}

#[derive(Debug)]
pub struct Regn {
    functions: HashMap<String, String>,
    variables: HashMap<String, String>,
}

#[derive(Debug)]
enum Expr {
    None,
    UnaryOperator(String, Box<Expr>),
    BinaryOperator(String, Box<Expr>, Box<Expr>),
    Function(String, Box<Expr>),
    Number(String),
}

impl Regn {
    fn new() -> Regn {
        Regn {
            functions: HashMap::new(),
            variables: HashMap::new(),
        }
    }

    fn parse_number(&self, s: &[char], mut idx: usize) -> Result<(usize, Expr), String> {
        eprintln!("parse_number");
        let mut buf = String::new();
        loop {
            match s.get(idx) {
                Some('0'..'9') | Some('.') | Some('e') => buf += s[idx].to_string().as_str(),
                _ => break,
            }
            idx += 1;
        }

        Ok((idx, Expr::Number(buf)))
    }

    fn parse_binary_operator(&self, s: &[char], mut idx: usize) -> Result<(usize, String), String> {
        eprintln!("parse_binary_operator");
        match s.get(idx) {
            Some('+') | Some('-') | Some('/') | Some('*') => Ok((idx+1, s[idx].to_string())),
            _ => Err("expected binary operator".to_string()),
        }
    }

    fn parse_unary_operator(&self, s: &[char], mut idx: usize) -> Result<(usize, String), String> {
        eprintln!("parse_unary_operator");
        match s.get(idx) {
            Some('+') | Some('-') | Some('/') | Some('*') => Ok((idx+1, s[idx].to_string())),
            _ => Err("expected unary operator".to_string()),
        }
    }

    fn parse_function(&self, s: &[char], mut idx: usize) -> Result<(usize, String), String> {
        eprintln!("parse_function");
        let mut buf = String::new();
        loop {
            match s.get(idx) {
                Some('a'..'z') | Some('A'..'Z') => buf += s[idx].to_string().as_str(),
                _ => break,
            }
            idx += 1;
        }

        match self.functions.get(&buf) {
            Some(_) => Ok((idx, buf)),
            None => Err("no such function".to_string()),
        }
    }

    fn parse_variable(&self, s: &[char], mut idx: usize) -> Result<(usize, Expr), String> {
        eprintln!("parse_variable");
        let mut buf = String::new();
        loop {
            match s.get(idx) {
                Some('a'..'z') | Some('A'..'Z') => buf += s[idx].to_string().as_str(),
                _ => break,
            }
            idx += 1;
        }

        match self.variables.get(&buf) {
            Some(v) => Ok((idx, Expr::Number(v.to_string()))),
            None => Err("no such function".to_string()),
        }
    }

    fn parse_variable_or_function(&self, s: &[char], idx: usize) -> Result<(usize, Expr), String> {
        eprintln!("parse_variable_or_function");
        if let Ok(v) = self.parse_variable(s, idx) {
            return Ok(v);
        }

        match self.parse_function(s, idx) {
            Err(_) => return Err("unknown variable or function".to_string()),
            Ok((new_idx, func)) => {
                let (new_idx, val) = self.parse_expr(s, new_idx)?;
                Ok((new_idx, Expr::Function(func, Box::new(val))))
            }
        }
    }

    fn parse_subexpr_or_variable_or_number(&self, s: &[char], idx: usize) -> Result<(usize, Expr), String> {
        eprintln!("parse_variable_or_function");

        match s.get(idx) {
            Some('(') => self.parse_expr(s, idx+1),
            Some('0'..'9') | Some('.') => self.parse_number(s, idx),
            Some('a'..'z') | Some('A'..'Z') => self.parse_variable(s, idx),
            _ => Err("expected variable or number".to_string()),
        }
    }

    fn parse_expr(&self, s: &[char], mut idx: usize) -> Result<(usize, Expr), String> {
        eprintln!("parse_expr");
        while s.get(idx) == Some(&' ') {
            idx += 1;
        }

        let (new_idx, mut expr) = match s.get(idx) {
            Some('(') => self.parse_expr(s, idx+1)?,
            Some('0'..'9') | Some('.') => self.parse_number(s, idx)?,
            Some('a'..'z') | Some('A'..'Z') => self.parse_variable_or_function(s, idx)?,
            Some(_) => {
                let (new_idx, op) = self.parse_unary_operator(s, idx)?;
                let (new_idx, val) = self.parse_subexpr_or_variable_or_number(s, new_idx)?;
                (new_idx, Expr::UnaryOperator(op, Box::new(val)))
            },
            None => return Ok((idx, Expr::None)),
        };

        idx = new_idx;
        loop {
            while s.get(idx) == Some(&' ') {
                idx += 1;
            }

            let (new_idx, binary_op) = match s.get(idx) {
                Some(')') | None => return Ok((idx, expr)),
                Some(_) => self.parse_binary_operator(s, idx)?,
            };

            idx = new_idx;
            while s.get(idx) == Some(&' ') {
                idx += 1;
            }

            let (new_idx, right_expr) = match s.get(idx) {
                Some('(') => self.parse_expr(s, idx+1)?,
                Some('0'..'9') | Some('.') => self.parse_number(s, idx)?,
                Some('a'..'z') | Some('A'..'Z') => self.parse_variable(s, idx)?,
                Some(_) => {
                    let (new_idx, op) = self.parse_unary_operator(s, idx)?;
                    let (new_idx, val) = self.parse_expr(s, new_idx)?;
                    (new_idx, Expr::UnaryOperator(op, Box::new(val)))
                },
                None => return Err("expect right side of binary operator".to_string()),
            };

            idx = new_idx;
            expr = Expr::BinaryOperator(binary_op, Box::new(expr), Box::new(right_expr));
        }
    }

    fn parse(&self, s: &str) -> Result<Expr, String> {
        let (idx, expr) = self.parse_expr(&s.chars().collect::<Vec<char>>(), 0)?;
        Ok(expr)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        use crate::{Regn};
        let r = Regn::new();
        eprintln!("{:?}", r.parse("-( -1 + 2 / 3 )"));
        assert_eq!(false, true);
    }
}
