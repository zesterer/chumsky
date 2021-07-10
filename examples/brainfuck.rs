use chumsky::{Parser, just, recursive};
use std::{env, io::{self, Read}, fs};

#[derive(Clone)]
enum Instr {
    Invalid,
    Left, Right,
    Incr, Decr,
    Read, Write,
    Loop(Vec<Self>)
}

fn parser() -> impl Parser<char, Vec<Instr>> {
    use Instr::*;
    recursive(|bf| bf.delimited_by('[', ']').map(|xs| xs.map_or(Invalid, Loop))
        .or(just('<').to(Left))
        .or(just('>').to(Right))
        .or(just('+').to(Incr))
        .or(just('-').to(Decr))
        .or(just(',').to(Read))
        .or(just('.').to(Write))
        .repeated())
}

const TAPE_LEN: usize = 10_000;

/// Interpret a brainfuck AST
fn exec(ast: &[Instr], ptr: &mut usize, tape: &mut [u8; TAPE_LEN]) {
    use Instr::*;
    for symbol in ast {
        match symbol {
            Invalid => unreachable!(),
            Left => *ptr = (*ptr + TAPE_LEN - 1).rem_euclid(TAPE_LEN),
            Right => *ptr = (*ptr + 1).rem_euclid(TAPE_LEN),
            Incr => tape[*ptr] = tape[*ptr].wrapping_add(1),
            Decr => tape[*ptr] = tape[*ptr].wrapping_sub(1),
            Read => tape[*ptr] = io::stdin().bytes().next().unwrap().unwrap(),
            Write => print!("{}", tape[*ptr] as char),
            Loop(ast) => while tape[*ptr] != 0 { exec(ast, ptr, tape) },
        }
    }
}

fn main() {
    let src = fs::read_to_string(env::args().nth(1).expect("Expected file argument")).expect("Failed to read file");
    let ast = parser().parse(src.chars()).expect("Failed to parse");
    exec(&ast, &mut 0, &mut [0; TAPE_LEN]);
}
