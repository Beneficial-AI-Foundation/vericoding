//Given an array of characters, it filters all the vowels. [‘d’,’e’,’l’,’i’,’g’,’h’,’t’]-> [’e’,’i’]
const vowels: set<char> := {'a', 'e', 'i', 'o', 'u'}

function FilterVowels(xs: seq<char>): seq<char>
{
    if |xs| == 0 then []
    else if xs[|xs|-1] in vowels then FilterVowels(xs[..|xs|-1]) + [xs[|xs|-1]]
    else FilterVowels(xs[..|xs|-1])
}

// <vc-helpers>
// No helper functions needed.
// </vc-helpers>

// <vc-spec>
method FilterVowelsArray(xs: array<char>) returns (ys: array<char>)
    ensures fresh(ys)
    ensures FilterVowels(xs[..]) == ys[..]
// </vc-spec>
// <vc-code>
{
  var seqv := FilterVowels(xs[..]);
  var n := |seqv|;
  var arr := new char[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant arr[..i] == seqv[..i]
  {
    arr[i] := seqv[i];
    i := i + 1;
  }
  ys := arr;
}
// </vc-code>

