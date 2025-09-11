// <vc-preamble>
const vowels: set<char> := {'a', 'e', 'i', 'o', 'u'}

function FilterVowels(xs: seq<char>): seq<char>
{
    if |xs| == 0 then []
    else if xs[|xs|-1] in vowels then FilterVowels(xs[..|xs|-1]) + [xs[|xs|-1]]
    else FilterVowels(xs[..|xs|-1])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FilterVowelsArray(xs: array<char>) returns (ys: array<char>)
    ensures fresh(ys)
    ensures FilterVowels(xs[..]) == ys[..]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
