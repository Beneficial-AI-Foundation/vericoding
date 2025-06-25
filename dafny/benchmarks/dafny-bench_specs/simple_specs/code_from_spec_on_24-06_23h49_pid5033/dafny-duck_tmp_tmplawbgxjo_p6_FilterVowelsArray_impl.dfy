//ATOM
//Given an array of characters, it filters all the vowels. ['d','e','l','i','g','h','t']-> ['e','i']

const vowels: set<char> := {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}

function FilterVowels(xs: seq<char>): seq<char>
{
  if |xs| == 0 then []
  else if xs[|xs|-1] in vowels then FilterVowels(xs[..|xs|-1]) + [xs[|xs|-1]]
  else FilterVowels(xs[..|xs|-1])
}

//IMPL
method FilterVowelsArray(xs: array<char>) returns (ys: array<char>)
  ensures fresh(ys)
  ensures FilterVowels(xs[..]) == ys[..]
{
  var filtered := FilterVowels(xs[..]);
  ys := new char[|filtered|];
  
  var i := 0;
  while i < |filtered|
    invariant 0 <= i <= |filtered|
    invariant forall j :: 0 <= j < i ==> ys[j] == filtered[j]
  {
    ys[i] := filtered[i];
    i := i + 1;
  }
}