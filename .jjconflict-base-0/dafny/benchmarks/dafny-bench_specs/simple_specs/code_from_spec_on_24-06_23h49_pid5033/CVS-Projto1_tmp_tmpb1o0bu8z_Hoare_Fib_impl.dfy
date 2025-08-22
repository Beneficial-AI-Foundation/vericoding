//ATOM


datatype List<T> = Nil | Cons(head: T, tail: List<T>)


//ATOM



function fib (n: nat) : nat
{
  if n == 0 then 1 else
  if n == 1 then 1 else
  fib(n -1) + fib (n-2)
}


//IMPL 

method Fib (n: nat) returns (r:nat)
  ensures r == fib(n)
{
  if n == 0 {
    r := 1;
  } else if n == 1 {
    r := 1;
  } else {
    var a := Fib(n - 1);
    var b := Fib(n - 2);
    r := a + b;
  }
}