// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsPartialWord(word: string) { forall i :: 0 <= i < |word| ==> word[i] == '(' || word[i] == ')' }
// </vc-helpers>

// <vc-spec>
method split(s : string) returns (res : seq<string>)

    requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '

    ensures forall s1 :: s1 in res ==> (forall i :: i >= 0 && i < |s1| ==> s1[i] == '(' || s1[i] == ')') && |s1| > 0
// </vc-spec>
// <vc-code>
{
  res := [];
  var current_word := "";
  var i := 0;
  while i < |s|
    invariant i <= |s|
    invariant forall s1 :: s1 in res ==> IsPartialWord(s1) && |s1| > 0
    invariant IsPartialWord(current_word)
  {
    if s[i] == ' ' {
      if |current_word| > 0 {
        res := res + [current_word];
        current_word := "";
      }
    } else {
      current_word := current_word + [s[i]];
    }
    i := i + 1;
  }

  if |current_word| > 0 {
    res := res + [current_word];
  }
}
// </vc-code>
