/*
This example is based on this Rust program
https://github.com/TheAlgorithms/Rust/blob/master/src/ciphers/another_rot13.rs

It turns out that Verus' support for String is limited.
And, it was quite challenging to turn the original simple example into a Verus verifiable Rust program.

The original program only has one function. I split the "another_rot13" function into two, init and encrypt.
*/

use vstd::prelude::*;
use vstd::string::*;
 
verus!{

  fn main() {
    // TODO: Remove this comment and implement the function body
  }

   fn init (in_string: &mut StrSlice, out_string: &mut StrSlice)
   ensures
        in_string@.len() == out_string@.len(),
   {
    // TODO: Remove this comment and implement the function body
   }

    pub fn encrypt(text: &mut Vec<char>, in_string: &StrSlice, out_string: &StrSlice)
    requires
        in_string@.len() == out_string@.len(),
    {
    // TODO: Remove this comment and implement the function body
    }

}
