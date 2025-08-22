//ATOM
//Given an array of characters, it filters all the vowels. [‘d’,’e’,’l’,’i’,’g’,’h’,’t’]-> [’e’,’i’]

function FilterVowels(xs: seq<char>): seq<char>
{
  if |xs| == 0 then []
  else if xs[|xs|-1] in vowels then FilterVowels(xs[..|xs|-1]) + [xs[|xs|-1]]
  else FilterVowels(xs[..|xs|-1])
}


// SPEC

method FilterVowelsArray(xs: array<char>) returns (ys: array<char>)
  ensures fresh(ys)
  ensures FilterVowels(xs[..]) == ys[..]
{
}
