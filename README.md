# JAM RS: A Jam Language Interpreter

This is an interpreter for Jam, a pedagogical functional programming language created for COMP 411 at Rice University. For the most part, this project serves as a proof-of-concept of the validity of using the Rust programming language as a tool for making interpreters effectively.

## Usage

Right now, the executable for JAM RS is just a Hello, World. Additionally, none of the API has been publicly expoed yet. However, you can test programs by writing unit tests

## To-do

It's unclear that I'll get any of this done, but these are some possible areas for improvement.

- Find a way to handle mutation without creating reference cycles.
- Make compiled executable interpret files and/or stdin.
- Implement new types of `cons()`: by name, value, and need.
- Support typing.
- Wax your moustache!

## Contributing

Feel free to open a pull request. 

## License

This code is licensed under either the [MIT license](https://mit-license.org/) or the [Apache 2.0 license](https://apache.org/licenses/LICENSE-2.0), your choice.