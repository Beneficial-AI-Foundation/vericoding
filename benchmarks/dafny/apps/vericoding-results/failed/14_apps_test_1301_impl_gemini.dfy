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
function IndexOf(s: string, c: char): (idx: int)
  requires c in s
  ensures 0 <= idx < |s| && s[idx] == c
  ensures forall k :: 0 <= k < idx ==> s[k] != c
  decreases |s|
{
  if s[0] == c then 0 else 1 + IndexOf(s[1..], c)
}

function SplitLines(s: string): seq<string>
{
    if '\n' in s then
        var i := IndexOf(s, '\n');
        [s[..i], s[i+1..]]
    else
        [s]
}

lemma AllPokemonsAreValid()
    ensures forall i :: 0 <= i < |GetPokemonList()| ==> ValidPokemonName(GetPokemonList()[i])
{
    var pokemonList := GetPokemonList();
    forall i | 0 <= i < |pokemonList|
        ensures ValidPokemonName(pokemonList[i])
    {
    }
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

    assert exists j :: 0 <= j < |pokemonList| && |pokemonList[j]| == |pattern| && MatchesPattern(pokemonList[j], pattern);

    var i := 0;
    while i < |pokemonList|
      invariant 0 <= i <= |pokemonList|
      invariant forall j :: 0 <= j < i ==> (|pokemonList[j]| != |pattern| || !MatchesPattern(pokemonList[j], pattern))
    {
        var pokemon := pokemonList[i];
        if |pokemon| == |pattern| && MatchesPattern(pokemon, pattern) {
            AllPokemonsAreValid();
            return pokemon;
        }
        i := i + 1;
    }
    assert false;
}
// </vc-code>

