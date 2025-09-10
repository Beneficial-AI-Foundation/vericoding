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
lemma FirstMatchExists(lines: seq<string>, pokemonList: seq<string>)
    requires |lines| >= 2
    requires 6 <= |lines[1]| <= 8
    requires exists j :: 0 <= j < |pokemonList| && |pokemonList[j]| == |lines[1]| && MatchesPattern(pokemonList[j], lines[1])
    ensures exists i :: 0 <= i < |pokemonList| && 
        (|pokemonList[i]| == |lines[1]| &&
        MatchesPattern(pokemonList[i], lines[1]) &&
        forall j :: 0 <= j < i ==> (|pokemonList[j]| != |lines[1]| || !MatchesPattern(pokemonList[j], lines[1])))
{
    // Find the first matching index
    var i := 0;
    while i < |pokemonList|
        invariant 0 <= i <= |pokemonList|
        invariant forall k :: 0 <= k < i ==> (|pokemonList[k]| != |lines[1]| || !MatchesPattern(pokemonList[k], lines[1]))
        decreases |pokemonList| - i
    {
        if |pokemonList[i]| == |lines[1]| && MatchesPattern(pokemonList[i], lines[1]) {
            // Found the first match
            return;
        }
        i := i + 1;
    }
    // Should not reach here due to precondition
    assert false;
}

lemma MatchesPatternLength(pokemonName: string, pattern: string)
    requires |pokemonName| == |pattern|
    ensures MatchesPattern(pokemonName, pattern) == 
        (forall i :: 0 <= i < |pattern| ==> (pattern[i] == '.' || pattern[i] == pokemonName[i]))
{
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
  var split_index := input.IndexOf('\n');
  var line0 := input[0..split_index];
  var line1 := input[split_index+1..];
  var pattern := line1;
  var pokemonList := GetPokemonList();
  var index := 0;
  
  while index < |pokemonList|
    invariant 0 <= index <= |pokemonList|
    invariant forall j :: 0 <= j < index ==> (|pokemonList[j]| != |pattern| || !MatchesPattern(pokemonList[j], pattern))
    decreases |pokemonList| - index
  {
    var pokemon := pokemonList[index];
    if |pokemon| == |pattern| && MatchesPattern(pokemon, pattern) {
      result := pokemon;
      return;
    }
    index := index + 1;
  }
  
  // This should never happen due to the precondition ValidInput
  assert false;
}
// </vc-code>

