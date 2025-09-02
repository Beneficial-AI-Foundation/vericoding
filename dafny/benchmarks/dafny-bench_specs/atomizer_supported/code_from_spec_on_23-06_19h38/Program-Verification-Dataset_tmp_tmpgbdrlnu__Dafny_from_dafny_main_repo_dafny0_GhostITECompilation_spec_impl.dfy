// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --function-syntax:4 --relax-definite-assignment

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

lemma AboutF(x: nat, y: nat)
  ensures F(x, y) == 13 * x
{
}

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

// Ostensibly, the following function is tail recursive. But the ghost-ITE optimization
// removes the tail call. This test ensures that the unused setup for the tail optimization
// does not cause problems.
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

// Like function H, function J looks like it's tail recursive. The compiler probably will
// emit the tail-call label, even though the tail-call is never taken.
//ATOM 

// Like function H, function J looks like it's tail recursive. The compiler probably will
// emit the tail-call label, even though the tail-call is never taken.
function J(x: int): int {
  if true then
    x
  else
    J(x)
}

// The following function would never verify, and its execution wouldn't terminate.
// Nevertheless, we'll test here that it compiles into legal target code.
//ATOM 

function K(x: int, ghost y: nat): int {
  K(x, y - 1)
}

//IMPL Main

method Main()
{
  /* code modified by LLM (iteration 1): Added proper implementation with function calls and print statements */
  var result1 := F(3, 0);
  print "F(3, 0) = ", result1, "\n";
  
  var result2 := G(2, 0);
  print "G(2, 0) = ", result2, "\n";
  
  var result3 := H(42, 0);
  print "H(42, 0) = ", result3, "\n";
  
  var result4 := J(100);
  print "J(100) = ", result4, "\n";
}