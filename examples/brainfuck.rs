//! This is a Brainfuck parser and interpreter
//! Run it with the following command:
//! cargo run --example brainfuck -- examples/hello.bf

use chumsky::prelude::*;
use std::{env, io::{self, Read}, fs};

#[derive(Clone, Debug)]
enum Instr {
    Invalid,
    Left, Right,
    Incr, Decr,
    Read, Write,
    Loop(Vec<Self>)
}

fn parser() -> impl Parser<char, Vec<Instr>, Error = Simple<char>> {
    use Instr::*;
    recursive(|bf| bf.delimited_by('[', ']').map(Loop)
        // .recover_with(NestedDelimiters('[', ']'), || Invalid)
        .or(just('<').to(Left))
        .or(just('>').to(Right))
        .or(just('+').to(Incr))
        .or(just('-').to(Decr))
        .or(just(',').to(Read))
        .or(just('.').to(Write))
        .recover_with(SkipExcept([']']), || Invalid)
        .repeated())
    .then_ignore(end())
}

const TAPE_LEN: usize = 10_000;

fn execute(ast: &[Instr], ptr: &mut usize, tape: &mut [u8; TAPE_LEN]) {
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
            Loop(ast) => while tape[*ptr] != 0 { execute(ast, ptr, tape) },
        }
    }
}

fn main() {
    let src = fs::read_to_string(env::args().nth(1).expect("Expected file argument")).expect("Failed to read file");

    // let src = "[!]+";
    match parser().parse(src.trim()) {
        Ok(ast) => {
            println!("{:?}", ast);
            execute(&ast, &mut 0, &mut [0; TAPE_LEN])
        },
        Err(errs) => errs
            .into_iter()
            .for_each(|e| println!("{}", e)),
    }
}
