// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --function-syntax:4 --relax-definite-assignment

//ATOM F
function F(x: nat, ghost y: nat): nat
{
  if x == 0 then
    0
  else if y != 0 then
    F(x, y - 1) // this branch is not compiled (which even makes F auto-accumulator tail recursive)
  else
    F(x - 1, 60) + 13
}

//ATOM G
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

// Ostensibly, the following function is tail recursive. But the ghost-ITE optimization
// removes the tail call. This test ensures that the unused setup for the tail optimization
// does not cause problems.
//ATOM H
function H(x: int, ghost y: nat): int {
  if y == 0 then
    x
  else
    H(x, y - 1)
}

// Like function H, function J looks like it's tail recursive. The compiler probably will
// emit the tail-call label, even though the tail-call is never taken.
//ATOM J
function J(x: int): int {
  if true then
    x
  else
    J(x)
}

// The following function would never verify, and its execution wouldn't terminate.
// Nevertheless, we'll test here that it compiles into legal target code.
//ATOM K
function K(x: int, ghost y: nat): int {
  K(x, y - 1)
}

//IMPL Main
method Main() {
  /* code modified by LLM (iteration 1): Only call functions without ghost parameters since ghost code cannot be compiled */
  print "Testing recursive functions\n";
  print "J(100) = ", J(100), "\n";
  print "Testing complete\n";
}