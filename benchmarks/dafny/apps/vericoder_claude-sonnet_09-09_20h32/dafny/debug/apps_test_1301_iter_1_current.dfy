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
function SplitLines(s: string): seq<string>
{
    if |s| == 0 then []
    else
        var newlineIndex := FindNewline(s, 0);
        if newlineIndex == -1 then [s]
        else [s[0..newlineIndex]] + SplitLines(s[newlineIndex+1..])
}

function FindNewline(s: string, start: int): int
    requires 0 <= start <= |s|
{
    if start >= |s| then -1
    else if s[start] == '\n' then start
    else FindNewline(s, start + 1)
}

lemma GetPokemonListProperties()
    ensures var list := GetPokemonList();
    forall i :: 0 <= i < |list| ==> ValidPokemonName(list[i])
{
}

lemma FirstMatchExists(pattern: string, pokemonList: seq<string>)
    requires exists j :: 0 <= j < |pokemonList| && |pokemonList[j]| == |pattern| && MatchesPattern(pokemonList[j], pattern)
    ensures exists result :: IsFirstMatch(result, pattern, pokemonList)
{
    var i := 0;
    while i < |pokemonList|
        invariant 0 <= i <= |pokemonList|
    {
        if |pokemonList[i]| == |pattern| && MatchesPattern(pokemonList[i], pattern) {
            assert IsFirstMatch(pokemonList[i], pattern, pokemonList);
            return;
        }
        i := i + 1;
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
    
    GetPokemonListProperties();
    FirstMatchExists(pattern, pokemonList);
    
    var i := 0;
    while i < |pokemonList|
        invariant 0 <= i <= |pokemonList|
        invariant forall j :: 0 <= j < i ==> (|pokemonList[j]| != |pattern| || !MatchesPattern(pokemonList[j], pattern))
    {
        if |pokemonList[i]| == |pattern| && MatchesPattern(pokemonList[i], pattern) {
            result := pokemonList[i];
            assert IsFirstMatch(result, pattern, pokemonList);
            return;
        }
        i := i + 1;
    }
    
    assert false;
}
// </vc-code>

