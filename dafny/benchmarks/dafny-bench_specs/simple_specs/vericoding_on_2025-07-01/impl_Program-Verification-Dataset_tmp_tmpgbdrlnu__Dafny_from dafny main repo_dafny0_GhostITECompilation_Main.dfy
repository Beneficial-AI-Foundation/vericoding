Let me analyze what each function does:
- `F(5, 3)` should return 65
- `G(5, 3)` should return 65  
- `H(65, 3)` should return 65
- `J(65)` should return 65

The implementation is straightforward - I just need to call each function with the specified arguments and print the results followed by newlines.

//ATOM

function G(x: nat, ghost y: nat): nat
{
 if x == 0 then
  0
 else if y != 0 then
  var z := x + x;
  var a, b, c := 100, if x < z then G(x, y - 1) else G(x, y - 1), 200;
  b // this branch is not compiled (which even makes G auto-accumulator tail recursive)
 else
  G(x - 1, 60) + 13
}


//ATOM

// Like function H, function J looks like it's tail recursive. The compiler probably will
// emit the tail-call label, even though the tail-call is never taken.
function J(x: int): int {
 if true then
  x
 else
  J(x)
}


//ATOM
// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --function-syntax:4 --relax-definite-assignment

function F(x: nat, ghost y: nat): nat
{
 if x == 0 then
  0
 else if y != 0 then
  F(x, y - 1) // this branch is not compiled (which even makes F auto-accumulator tail recursive)
 else
  F(x - 1, 60) + 13
}


//ATOM

// Ostensibly, the following function is tail recursive. But the ghost-ITE optimization
// removes the tail call. This test ensures that the unused setup for the tail optimization
// does not cause problems.
function H(x: int, ghost y: nat): int {
 if y == 0 then
  x
 else
  H(x, y - 1)
}


//IMPL

method Main() {
 print F(5, 3), "\n"; // 65
 print G(5, 3), "\n"; // 65
 print H(65, 3), "\n"; // 65
 print J(65), "\n"; // 65
}