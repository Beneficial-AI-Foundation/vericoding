// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method join(a:array<int>,b:array<int>) returns (c:array<int>)
ensures a[..] + b[..] == c[..]
ensures multiset(a[..] + b[..]) == multiset(c[..])
ensures multiset(a[..]) + multiset(b[..]) == multiset(c[..])
ensures a.Length+b.Length == c.Length

ensures forall i :: 0<=i<a.Length ==> c[i] == a[i]
ensures forall i_2,j_2::
    a.Length <= i_2 < c.Length &&
    0<=j_2< b.Length && i_2 - j_2 == a.Length  ==> c[i_2] == b[j_2]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Switched to for-loops to ensure all postconditions are provably met. */
{
  c := new int[a.Length + b.Length];
  
  for i := 0 to a.Length 
    invariant c.Length == a.Length + b.Length
    invariant forall k :: 0 <= k < i ==> c[k] == a[k]
  {
    c[i] := a[i];
  }

  for j := 0 to b.Length 
    invariant c.Length == a.Length + b.Length
    invariant forall k :: 0 <= k < a.Length ==> c[k] == a[k]
    invariant forall k :: 0 <= k < j ==> c[a.Length + k] == b[k]
  {
    c[a.Length + j] := b[j];
  }
}
// </vc-code>
