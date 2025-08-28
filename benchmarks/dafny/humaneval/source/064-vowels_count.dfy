method vowel_count(s: string) returns (count: int)
  // post-conditions-start
  ensures count >= 0
  ensures count == |(set i | 0 <= i < |s| && is_vowel(s[i]))| + if |s| > 0 && s[|s| - 1] == 'y' then 1 else 0
  // post-conditions-end
{
    // impl-start
    ghost var found := {};
    count := 0;
    var i := 0;
    while i < |s|
      // invariants-start
      invariant 0 <= i <= |s|
      invariant count == |found|
      invariant forall j :: 0 <= j < i && is_vowel(s[j]) ==> j in found
      invariant forall x :: x in found ==> x < i
      invariant found == (set j | 0 <= j < i && is_vowel(s[j]))
      // invariants-end
    {
        if is_vowel(s[i]) {
            found := found + {i};
            count := count + 1;
        }
        i := i + 1;
    }
    count := count + if |s| > 0 && s[|s| - 1] == 'y' then 1 else 0;
    // impl-end
}

function is_vowel(c: char): bool
  ensures is_vowel(c) <==> c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
// pure-end
