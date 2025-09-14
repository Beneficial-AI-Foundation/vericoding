

// <vc-helpers>
lemma lemma_not_in_empty(s: seq<char>, c: char)
  ensures !(c in s) ==> forall i | 0 <= i < |s| :: s[i] != c
{
}

lemma lemma_found_first(s: seq<char>, c: char, idx: int)
  requires 0 <= idx < |s|
  requires s[idx] == c
  requires forall i | 0 <= i < idx :: s[i] != c
  ensures c in s
  ensures forall i | 0 <= i < idx :: s[i] != c
{
}
// </vc-helpers>

// <vc-spec>
method firstE(a: array<char>) returns (x: int)
ensures if 'e' in a[..] then 0 <= x < a.Length && a[x] == 'e' && forall i | 0 <= i < x :: a[i] != 'e' else x == -1
// </vc-spec>
// <vc-code>
{
  x := -1;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant x == -1 ==> forall j | 0 <= j < i :: a[j] != 'e'
    invariant x != -1 ==> (0 <= x < i && a[x] == 'e' && forall j | 0 <= j < x :: a[j] != 'e')
  {
    if a[i] == 'e' {
      x := i;
      break;
    }
    i := i + 1;
  }
}
// </vc-code>

