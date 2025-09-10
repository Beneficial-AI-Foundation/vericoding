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
lemma PokemonListValid()
  ensures forall p :: p in GetPokemonList() ==> ValidPokemonName(p)
{}

lemma MatchesSymmetric(pokemonName: string, pattern: string)
  requires |pokemonName| == |pattern|
  requires MatchesPattern(pokemonName, pattern)
  ensures MatchesPattern(pattern, pokemonName)
{}

function SplitLines(s: string): seq<string>
  decreases |s|
{
  if |s| == 0 then [] 
  else if |s| >= 1 && s[0] == '\n' then [[]] + SplitLines(s[1..])
  else if var pos := FindFirstNewline(s);
         pos < |s| then [s[..pos]] + SplitLines(s[pos+1..])
       else [s]
}

function FindFirstNewline(s: string): int
  decreases |s|
{
  if |s| == 0 then |s|
  else if s[0] == '\n' then 0
  else 1 + FindFirstNewline(s[1..])
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
    invariant forall j :: 0 <= j < i ==> !( |pokemonList[j]| == |pattern| && MatchesPattern(pokemonList[j], pattern) )
  {
    if |pokemonList[i]| == |pattern| && MatchesPattern(pokemonList[i], pattern)
    {
      result := pokemonList[i];
      return;
    }
    i := i + 1;
  }
  assert false;
}
// </vc-code>

