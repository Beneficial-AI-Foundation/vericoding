//Given an array of characters, it filters all the vowels. [‘d’,’e’,’l’,’i’,’g’,’h’,’t’]-> [’e’,’i’]
const vowels: set<char> := {'a', 'e', 'i', 'o', 'u'}

function FilterVowels(xs: seq<char>): seq<char>
{
    if |xs| == 0 then []
    else if xs[|xs|-1] in vowels then FilterVowels(xs[..|xs|-1]) + [xs[|xs|-1]]
    else FilterVowels(xs[..|xs|-1])
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FilterVowelsArray(xs: array<char>) returns (ys: array<char>)
    ensures fresh(ys)
    ensures FilterVowels(xs[..]) == ys[..]
// </vc-spec>
// <vc-code>
{
  var s := FilterVowels(xs[..]);
  ys := new char[|s|];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant ys.Length == |s|
    invariant forall j :: 0 <= j < i ==> ys[j] == s[j]
    decreases |s| - i
  {
    ys[i] := s[i];
    i := i + 1;
  }
}
// </vc-code>

