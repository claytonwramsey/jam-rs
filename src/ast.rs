//! A module for definining abstract syntax trees of the Jam language.

use std::{borrow::Borrow, fmt::Display, rc::Rc};

#[allow(unused)]
#[derive(Clone, Debug, PartialEq, Eq)]
/// An AST (abstract syntax tree).
pub enum Ast {
    /// An integer literal. Will always be positive (as negatives are actually
    /// operators).
    Int(u32),
    /// A boolean literal.
    Bool(bool),
    /// A variable.
    Variable(String),
    /// A primitive function.
    Primitive(PrimFun),
    /// The unit empty list.
    Empty,
    /// The application of a function.
    App {
        /// The function being called.
        rator: Rc<Ast>,
        /// The parameters to the function.
        params: Vec<Rc<Ast>>,
    },
    /// The application of a binary operation.
    BinOp {
        /// The operator being used.
        rator: BinOp,
        /// The left hand side.
        lhs: Rc<Ast>,
        /// The right hand side.
        rhs: Rc<Ast>,
    },
    /// The application of a unary operation.
    UnOp {
        /// The operator.
        rator: UnOp,
        /// The operand.
        operand: Rc<Ast>,
    },
    /// An if statement.
    If {
        /// The condition of the if.
        condition: Rc<Ast>,
        /// The result if the condition is true.
        consequence: Rc<Ast>,
        /// The result if the condition is false.
        alternate: Rc<Ast>,
    },
    /// A let statement.
    Let {
        /// The variables defined. Each element is a (identifier, contents)
        /// pair.
        defs: Vec<(String, Rc<Ast>)>,
        /// The body of the let statement which is evaluated with the bindings
        /// in the defs.
        body: Rc<Ast>,
    },
    /// A function definition.
    Map {
        /// The parameters, in order.
        params: Vec<String>,
        /// The body of the map.
        body: Rc<Ast>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// The set of all binary operations. Typically used with an `lhs` and a `rhs`.
pub enum BinOp {
    /// The sum of `lhs` and `rhs`.
    Plus,
    /// The difference of `lhs` and `rhs`.
    Minus,
    /// Divide.
    Div,
    /// Multiply.
    Mul,
    /// Logical and.
    And,
    /// Logical or.
    Or,
    /// Equality.
    Eq,
    /// Inequality.
    Neq,
    /// Greater than.
    Gt,
    /// Greater than or equal to.
    Geq,
    /// Less than.
    Lt,
    /// Less than or equal to.
    Leq,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// The set of unary operators.
pub enum UnOp {
    /// Logical not.
    Not,
    /// Integer negation.
    Neg,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// The set of provided primitive functions.
pub enum PrimFun {
    /// Takes 1 argument. Returns `true` if the argument is a number, and
    /// `false` otherwise.
    IsNumber,
    /// Takes 1 argument. Returns `true` if the argument is a function, and
    /// `false` otherwise.
    IsFunction,
    /// Takes 1 argument. Returns `true` if the argument is a list, and `false`
    /// otherwise.
    IsList,
    /// Takes 1 argument. Returns `true` if the argument is an empty list, and
    /// `false` otherwise.
    IsEmpty,
    /// Takes 1 argument. Returns `true` if the argument is a non-empty list,
    /// and `false` otherwise.
    IsCons,
    /// Takes 2 arguments. The second argument must be a list. Constructs a
    /// list containing the first argument as its head and the second argument
    /// as its remainder.
    Cons,
    /// Takes 1 argument. The argument must be a list. Returns the head of the
    /// list.
    First,
    /// Takes 1 argument. The argument must be a list. Returns the rest of the
    /// list.
    Rest,
    /// Takes 1 argument. The argument must be a function. Returns the number
    /// of arguments taken by the function.
    Arity,
}

impl Display for Ast {
    /// Print out the program. The displayed version of this program should be
    /// able to be parsed and yield an identical AST.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ast::Int(n) => write!(f, "{n}"),
            Ast::Bool(b) => write!(f, "{b}"),
            Ast::Variable(v) => write!(f, "{}", &v),
            Ast::Empty => write!(f, "empty"),
            Ast::App { rator, params } => {
                match rator.borrow() {
                    Ast::Variable(v) => write!(f, "{v}("),
                    Ast::Primitive(p) => write!(f, "{p}("),
                    _ => write!(f, "({rator})("),
                }?;
                write_list(params, ", ", f)?;
                write!(f, ")")
            }
            Ast::BinOp { rator, lhs, rhs } => write!(f, "{lhs} {rator} {rhs}"),
            Ast::UnOp { rator, operand } => write!(f, "{rator}{operand}"),
            Ast::If {
                condition,
                consequence,
                alternate,
            } => write!(f, "if {condition} then {consequence} else {alternate}"),
            Ast::Let { defs, body } => {
                write!(f, "let ")?;
                for def in defs {
                    write!(f, "{} := {}; ", def.0, def.1)?;
                }
                write!(f, "in {body}")
            }
            Ast::Map { params, body } => {
                write!(f, "map ")?;
                write_list(params, ", ", f)?;
                write!(f, " to {body}")
            }
            Ast::Primitive(fun) => write!(f, "{fun}"),
        }
    }
}

impl Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                UnOp::Not => "~",
                UnOp::Neg => "-",
            }
        )
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                BinOp::Plus => "+",
                BinOp::Minus => "-",
                BinOp::Div => "/",
                BinOp::Mul => "*",
                BinOp::And => "&",
                BinOp::Or => "|",
                BinOp::Eq => "=",
                BinOp::Neq => "!=",
                BinOp::Gt => ">",
                BinOp::Geq => ">=",
                BinOp::Lt => "<",
                BinOp::Leq => "<=",
            }
        )
    }
}

impl Display for PrimFun {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match *self {
                PrimFun::IsNumber => "number?",
                PrimFun::IsFunction => "function?",
                PrimFun::IsList => "list?",
                PrimFun::IsEmpty => "empty?",
                PrimFun::IsCons => "cons?",
                PrimFun::Cons => "cons",
                PrimFun::First => "first",
                PrimFun::Rest => "rest",
                PrimFun::Arity => "arity",
            }
        )
    }
}

/// Helper function for writing out a list of statements, separated by a
/// string.
pub fn write_list<T: Display>(
    list: &[T],
    sep: &str,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    match list.len() {
        0 => Ok(()),
        1 => write!(f, "{}", list[0]),
        _ => {
            write!(f, "{}", list[0])?;
            for elem in &list[1..] {
                write!(f, "{sep}{elem}")?;
            }

            Ok(())
        }
    }
}
