#![feature(exclusive_range_pattern)]

use std::collections::HashMap;
use std::fmt;

#[derive(Debug)]
pub enum Value {
    Rat(i64, i64),
    Int(i64),
    Float(f64),
}

pub struct Function {
    name: String,
    args: usize,
    f: Box<dyn Fn(&[Expr]) -> Expr>,
}

impl fmt::Debug for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

pub struct BinaryOperator {
    name: String,
    precedence: usize,
    f: Box<dyn Fn(Expr, Expr) -> Expr>,
}

impl fmt::Debug for BinaryOperator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

pub struct UnaryOperator {
    name: String,
    f: Box<dyn Fn(Expr) -> Expr>,
}

impl fmt::Debug for UnaryOperator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Debug)]
pub struct Regn {
    functions: HashMap<String, Function>,
    variables: HashMap<String, String>,
    binary_operators: HashMap<String, BinaryOperator>,
    unary_operators: HashMap<String, UnaryOperator>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum Expr {
    None,
    Expr(Box<Expr>),
    UnaryOperator(String, Box<Expr>),
    BinaryOperator(String, Box<Expr>, Box<Expr>),
    Function(String, Box<Expr>),
    Number(String),
}

impl Regn {
    fn new() -> Regn {
        let mut r = Regn {
            functions: HashMap::new(),
            variables: HashMap::new(),
            unary_operators: HashMap::new(),
            binary_operators: HashMap::new(),
        };

        r.binary_operators.insert("+".to_string(), BinaryOperator{
            name: "+".to_string(),
            precedence: 10,
            f: Box::new(|_, _| Expr::None),
        });
        r.binary_operators.insert("-".to_string(), BinaryOperator{
            name: "-".to_string(),
            precedence: 10,
            f: Box::new(|_, _| Expr::None),
        });
        r.binary_operators.insert("*".to_string(), BinaryOperator{
            name: "*".to_string(),
            precedence: 20,
            f: Box::new(|_, _| Expr::None),
        });
        r.binary_operators.insert("/".to_string(), BinaryOperator{
            name: "/".to_string(),
            precedence: 20,
            f: Box::new(|_, _| Expr::None),
        });
        r.unary_operators.insert("-".to_string(), UnaryOperator{
            name: "-".to_string(),
            f: Box::new(|_| Expr::None),
        });
        r.unary_operators.insert("+".to_string(), UnaryOperator{
            name: "+".to_string(),
            f: Box::new(|_| Expr::None),
        });

        r
    }

    fn parse_num(&self, s: &[char], mut idx: usize) -> Result<(usize, Expr), String> {
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

    fn parse_binary_op(&self, s: &[char], mut idx: usize) -> Result<(usize, String), String> {
        match s.get(idx) {
            Some(op) => match self.binary_operators.get(&op.to_string()) {
                Some(_) => Ok((idx+1, op.to_string())),
                _ => Err("expected binary operator".to_string()),
            },
            _ => Err("expected binary operator".to_string()),
        }
    }

    fn parse_unary_op(&self, s: &[char], mut idx: usize) -> Result<(usize, String), String> {
        match s.get(idx) {
            Some(op) => match self.unary_operators.get(&op.to_string()) {
                Some(_) => Ok((idx+1, op.to_string())),
                _ => Err("expected unary operator".to_string()),
            },
            _ => Err("expected unary operator".to_string()),
        }
    }

    fn parse_func(&self, s: &[char], mut idx: usize) -> Result<(usize, String), String> {
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

    fn parse_var(&self, s: &[char], mut idx: usize) -> Result<(usize, Expr), String> {
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

    fn parse_subexpr_var_num(&self, s: &[char], idx: usize) -> Result<(usize, Expr), String> {

        match s.get(idx) {
            Some('(') => self.parse_expr(s, idx+1),
            Some('0'..'9') | Some('.') => self.parse_num(s, idx),
            Some('a'..'z') | Some('A'..'Z') => self.parse_var(s, idx),
            _ => Err("expected variable or number".to_string()),
        }
    }

    fn parse_unary_var_func(&self, s: &[char], idx: usize) -> Result<(usize, Expr), String> {
        if let Ok((new_idx, op)) = self.parse_unary_op(s, idx) {
            let (new_idx, val) = self.parse_subexpr_var_num(s, new_idx)?;
            return Ok((new_idx, Expr::UnaryOperator(op, Box::new(val))));
        }

        if let Ok(v) = self.parse_var(s, idx) {
            return Ok(v);
        }

        match self.parse_func(s, idx) {
            Err(_) => return Err("unknown variable or function".to_string()),
            Ok((new_idx, func)) => {
                let (new_idx, val) = self.parse_expr(s, new_idx)?;
                Ok((new_idx, Expr::Function(func, Box::new(val))))
            }
        }
    }

    fn parse_expr(&self, s: &[char], mut idx: usize) -> Result<(usize, Expr), String> {
        while s.get(idx) == Some(&' ') {
            idx += 1;
        }

        // Process left-hand expression
        let (new_idx, mut expr) = match s.get(idx) {
            Some('(') => self.parse_expr(s, idx+1)?,
            Some('0'..'9') | Some('.') => self.parse_num(s, idx)?,
            Some(_) => self.parse_unary_var_func(s, idx)?,
            None => return Err("expected expression".to_string()),
        };

        idx = new_idx;
        loop {
            while s.get(idx) == Some(&' ') {
                idx += 1;
            }

            // Check if we have a binary operator or if we're done
            let (new_idx, binary_op) = match s.get(idx) {
                Some(')') | None => break,
                Some(_) => self.parse_binary_op(s, idx)?,
            };

            idx = new_idx;
            while s.get(idx) == Some(&' ') {
                idx += 1;
            }

            // Parse the right-hand side of the binary operator
            let (new_idx, right_expr) = match s.get(idx) {
                Some('(') => self.parse_expr(s, idx+1)?,
                Some('0'..'9') | Some('.') => self.parse_num(s, idx)?,
                Some(_) => self.parse_unary_var_func(s, idx)?,
                None => return Err("expect right side of binary operator".to_string()),
            };

            idx = new_idx;

            // Replace our left-hand expression with the binary operation, so
            // we can look for more binary operators.
            expr = Expr::BinaryOperator(binary_op, Box::new(expr), Box::new(right_expr));
        }

        Ok((idx, Expr::Expr(Box::new(expr))))
    }

    fn reorder_expr(&self, expr: Expr) -> Expr {
        match expr {
            Expr::BinaryOperator(outer_op_name, outer_left, outer_right) => {
                let outer_op = match self.binary_operators.get(&outer_op_name) {
                    Some(op) => op,
                    None => panic!("failed invariant: we should not have unknown operators at this stage"),
                };

                let outer_left = self.reorder_expr(*outer_left);
                let outer_right = self.reorder_expr(*outer_right);

                if let Expr::BinaryOperator(..) = outer_right {
                    panic!("failed invariant: we should not end up with a binary operator as right-hand side of another binary operator at this stage")
                }

                match outer_left {
                    Expr::BinaryOperator(left_op_name, left_left, left_right) => {
                        let left_op = match self.binary_operators.get(&left_op_name) {
                            Some(op) => op,
                            None => panic!("failed invariant: we should not have unknown operators at this stage"),
                        };

                        if outer_op.precedence > left_op.precedence {
                            // Okay, we need to swap the operators.
                            // This part looks a bit confusing.
                            Expr::BinaryOperator(
                                left_op_name,
                                left_left,
                                Box::new(Expr::BinaryOperator(
                                    outer_op_name,
                                    left_right,
                                    Box::new(outer_right)))
                            )
                        } else {
                            Expr::BinaryOperator(
                                outer_op_name,
                                Box::new(Expr::BinaryOperator(
                                    left_op_name,
                                    left_left,
                                    left_right)),
                                Box::new(outer_right),
                            )
                        }
                    },
                    v => {

                        Expr::BinaryOperator(
                            outer_op_name,
                            Box::new(v),
                            Box::new(outer_right),
                        )
                    }
                }

            },
            Expr::Expr(expr) => {
                Expr::Expr(Box::new(self.reorder_expr(*expr)))
            },
            Expr::UnaryOperator(op, expr) => {
                Expr::UnaryOperator(op, Box::new(self.reorder_expr(*expr)))
            },
            expr => expr,
        }
    }

    fn parse(&self, s: &str) -> Result<Expr, String> {
        let (idx, expr) = self.parse_expr(&s.chars().collect::<Vec<char>>(), 0)?;
        Ok(self.reorder_expr(expr))
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn simple() {
        use crate::{Regn, Expr};
        let r = Regn::new();
        assert_eq!(r.parse("1+2"), Ok(
            Expr::Expr(
                Box::new(Expr::BinaryOperator(
                    "+".to_string(),
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("2".to_string())))))));

        assert_eq!(r.parse("(1+2)"), Ok(
            Expr::Expr(
                Box::new(Expr::Expr(
                    Box::new(Expr::BinaryOperator(
                        "+".to_string(),
                        Box::new(Expr::Number("1".to_string())),
                        Box::new(Expr::Number("2".to_string())))))))));

        assert_eq!(r.parse("-1"), Ok(
            Expr::Expr(
                Box::new(Expr::UnaryOperator(
                    "-".to_string(),
                    Box::new(Expr::Number("1".to_string())))))));
    }

    #[test]
    fn operator_precedence() {
        use crate::{Regn, Expr};
        let r = Regn::new();
        assert_eq!(r.parse("1+2*3"), Ok(
            Expr::Expr(
                Box::new(Expr::BinaryOperator(
                    "+".to_string(),
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::BinaryOperator(
                        "*".to_string(),
                        Box::new(Expr::Number("2".to_string())),
                        Box::new(Expr::Number("3".to_string())))))))));

        assert_eq!(r.parse("1*2+3"), Ok(
            Expr::Expr(
                Box::new(Expr::BinaryOperator(
                    "+".to_string(),
                    Box::new(Expr::BinaryOperator(
                        "*".to_string(),
                        Box::new(Expr::Number("1".to_string())),
                        Box::new(Expr::Number("2".to_string())))),
                    Box::new(Expr::Number("3".to_string())))))));

        assert_eq!(r.parse("1*(2+3)"), Ok(
            Expr::Expr(
                Box::new(Expr::BinaryOperator(
                    "*".to_string(),
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Expr(
                        Box::new(Expr::BinaryOperator(
                            "+".to_string(),
                            Box::new(Expr::Number("2".to_string())),
                            Box::new(Expr::Number("3".to_string())))))))))));

        // TODO: More tests here! Nexted and stuff!
    }
}

/*

    (  1 + 2  * 3 )

    Bin("*", Bin("+", 1, 2), 3)

    Bin("+", 1, Bin("*", 2, 3))

    (  1 * 2  + 3 )

    Bin("*", 1, Bin("+", 2, 3))

    Bin("+", Bin("*", 1, 2), 3)


    ( 1 * 2 + 3 * 4 )


    Bin("*", Bin("+", Bin("*", 1, 2), 3), 4)

    Bin("+", Bin("*", 1, 2), Bin("*", 3, 4))


    Bin("+", Bin("*", 1, 2))
*/