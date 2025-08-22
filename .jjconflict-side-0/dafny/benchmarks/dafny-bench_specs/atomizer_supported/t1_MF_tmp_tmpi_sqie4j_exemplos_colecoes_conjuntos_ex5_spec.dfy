// ATOM 
function to_seq<T>(a: array<T>, i: int) : (res: seq<T>)
requires 0 <= i <= a.Length
ensures res == a[i..]
reads a
{
  if i == a.Length
  then []
  else [a[i]] + to_seq(a, i + 1)
}


// SPEC 

method Main() {
}


