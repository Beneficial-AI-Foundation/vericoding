predicate ValidPokemonName(name: string)
{
    name == "vaporeon" || name == "jolteon" || name == "flareon" || name == "espeon" ||
    name == "umbreon" || name == "leafeon" || name == "glaceon" || name == "sylveon"
}

predicate MatchesPattern(pokemonName: string, pattern: string)
    requires |pokemonName| == |pattern|
{
    forall i :: 0 <= i < |pattern| ==> (pattern[i] == '.' || pattern[i] == pokemonName[i])
}

function GetPokemonList(): seq<string>
{
    ["vaporeon", "jolteon", "flareon", "espeon", "umbreon", "leafeon", "glaceon", "sylveon"]
}

predicate ValidInput(input: string)
{
    |input| > 0 && 
    var lines := SplitLines(input);
    |lines| >= 2 &&
    (|lines[0]| > 0 && forall i :: 0 <= i < |lines[0]| ==> '0' <= lines[0][i] <= '9') &&
    6 <= |lines[1]| <= 8 &&
    forall i :: 0 <= i < |lines[1]| ==> ('a' <= lines[1][i] <= 'z' || lines[1][i] == '.') &&
    exists j :: 0 <= j < |GetPokemonList()| && |GetPokemonList()[j]| == |lines[1]| && MatchesPattern(GetPokemonList()[j], lines[1])
}

predicate IsFirstMatch(result: string, pattern: string, pokemonList: seq<string>)
{
    exists i :: 0 <= i < |pokemonList| && 
        pokemonList[i] == result &&
        |result| == |pattern| &&
        MatchesPattern(result, pattern) &&
        forall j :: 0 <= j < i ==> (|pokemonList[j]| != |pattern| || !MatchesPattern(pokemonList[j], pattern))
}

// <vc-helpers>
function FirstNewlineFrom(s: string, i: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
  ensures i <= FirstNewlineFrom(s, i) <= |s|
{
  if i >= |s| then |s|
  else if s[i] == '\n' then i else FirstNewlineFrom(s, i+1)
}

function SplitFrom(s: string, i: int): seq<string>
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i >= |s| then []
  else var j := FirstNewlineFrom(s, i);
       assert 0 <= i <= j <= |s|;
       if j == |s| then [s[i..j]] else [s[i..j]] + SplitFrom(s, j+1)
}

function SplitLines(s: string): seq<string>
{
  SplitFrom(s, 0)
}

lemma ExtractMatchingIndex(input: string) returns (kk: int)
  requires ValidInput(input)
  ensures 0 <= kk < |GetPokemonList()|
  ensures |GetPokemonList()[kk]| == |SplitLines(input)[1]|
  ensures MatchesPattern(GetPokemonList()[kk], SplitLines(input)[1])
{
  var lines := SplitLines(input);
  var pokemonList := GetPokemonList();
  var i := 0;
  while i < |pokemonList|
    decreases |pokemonList| - i
  {
    if |pokemonList[i]| == |lines[1]| && MatchesPattern(pokemonList[i], lines[1]) {
      kk := i;
      return;
    }
    i := i + 1;
  }
  // No match found among the pokemon list -> contradiction with ValidInput
  assert exists j :: 0 <= j < |pokemonList| && |pokemonList[j]| == |lines[1]| && MatchesPattern(pokemonList[j], lines[1]);
  assert false;
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidPokemonName(result)
    ensures var lines := SplitLines(input);
        IsFirstMatch(result, lines[1], GetPokemonList())
    ensures var lines := SplitLines(input);
        exists i :: 0 <= i < |GetPokemonList()| && 
            GetPokemonList()[i] == result &&
            |result| == |lines[1]| &&
            MatchesPattern(result, lines[1])
// </vc-spec>
// <vc-code>
{
  var lines := SplitLines(input);
  var pattern := lines[1];
  var pokemonList := GetPokemonList();
  var i := 0;
  while i < |pokemonList|
    invariant 0 <= i <= |pokemonList|
    invariant forall j :: 0 <= j < i ==> (|pokemonList[j]| != |pattern| || !MatchesPattern(pokemonList[j], pattern))
  {
    if |pokemonList[i]| == |pattern| && MatchesPattern(pokemonList[i], pattern) {
      result := pokemonList[i];
      return;
    }
    i := i + 1;
  }
  // Loop terminated without finding a match: derive contradiction from ValidInput
  assert i == |pokemonList|;
  var kk := ExtractMatchingIndex(input);
  assert 0 <= kk < |pokemonList|;
  assert kk < i;
  assert forall j :: 0 <= j < i ==> (|pokemonList[j]| != |pattern| || !MatchesPattern(pokemonList[j], pattern));
  assert (|pokemonList[kk]| != |pattern| || !MatchesPattern(pokemonList[kk], pattern)) == false;
  assert false;
}
// </vc-code>

