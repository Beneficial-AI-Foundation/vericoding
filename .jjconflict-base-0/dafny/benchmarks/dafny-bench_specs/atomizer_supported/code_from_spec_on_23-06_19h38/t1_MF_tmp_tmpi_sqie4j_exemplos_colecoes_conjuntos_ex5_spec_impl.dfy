// ATOM 
function to_seq<T>(a: array<T>, i: int) : (res: seq<T>)
requires 0 <= i <= a.Length
ensures res == a[i..]
reads a
/* code modified by LLM (iteration 1): added decreases clause to ensure termination */
decreases a.Length - i
{
  if i == a.Length
  then []
  else [a[i]] + to_seq(a, i + 1)
}

// IMPL 
method Main() {
}