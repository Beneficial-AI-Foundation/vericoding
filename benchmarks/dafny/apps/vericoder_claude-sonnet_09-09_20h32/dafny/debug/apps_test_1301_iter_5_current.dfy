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
    decreases |s|
{
    if |s| == 0 then []
    else
        var newlineIndex := FindNewline(s, 0);
        if newlineIndex == -1 then [s]
        else if newlineIndex < |s| && newlineIndex + 1 <= |s| then [s[0..newlineIndex]] + SplitLines(s[newlineIndex+1..])
        else [s[0..newlineIndex]]
}

function FindNewline(s: string, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
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
    var firstMatchIndex := FindFirstMatchIndex(pattern, pokemonList, 0);
    assert IsFirstMatch(pokemonList[firstMatchIndex], pattern, pokemonList);
}

function FindFirstMatchIndex(pattern: string, pokemonList: seq<string>, start: int): int
    requires 0 <= start <= |pokemonList|
    requires exists j :: start <= j < |pokemonList| && |pokemonList[j]| == |pattern| && MatchesPattern(pokemonList[j], pattern)
    ensures start <= FindFirstMatchIndex(pattern, pokemonList, start) < |pokemonList|
    ensures |pokemonList[FindFirstMatchIndex(pattern, pokemonList, start)]| == |pattern|
    ensures MatchesPattern(pokemonList[FindFirstMatchIndex(pattern, pokemonList, start)], pattern)
    ensures forall k :: start <= k < FindFirstMatchIndex(pattern, pokemonList, start) ==> (|pokemonList[k]| != |pattern| || !MatchesPattern(pokemonList[k], pattern))
    decreases |pokemonList| - start
{
    if start >= |pokemonList| then start
    else if |pokemonList[start]| == |pattern| && MatchesPattern(pokemonList[start], pattern) then start
    else FindFirstMatchIndex(pattern, pokemonList, start + 1)
}

lemma LoopInvariantPreservation(pattern: string, pokemonList: seq<string>, i: int)
    requires 0 <= i < |pokemonList|
    requires forall j :: 0 <= j < i ==> (|pokemonList[j]| != |pattern| || !MatchesPattern(pokemonList[j], pattern))
    requires exists j :: i <= j < |pokemonList| && |pokemonList[j]| == |pattern| && MatchesPattern(pokemonList[j], pattern)
    requires |pokemonList[i]| != |pattern| || !MatchesPattern(pokemonList[i], pattern)
    ensures exists j :: (i+1) <= j < |pokemonList| && |pokemonList[j]| == |pattern| && MatchesPattern(pokemonList[j], pattern)
{
}

lemma ValidInputImpliesMatchExists(input: string)
    requires ValidInput(input)
    ensures var lines := SplitLines(input);
        exists j :: 0 <= j < |GetPokemonList()| && |GetPokemonList()[j]| == |lines[1]| && MatchesPattern(GetPokemonList()[j], lines[1])
{
    var lines := SplitLines(input);
}

lemma ValidInputMatchExistsDetail(input: string)
    requires ValidInput(input)
    ensures var lines := SplitLines(input);
        var pattern := lines[1];
        var pokemonList := GetPokemonList();
        exists j :: 0 <= j < |pokemonList| && |pokemonList[j]| == |pattern| && MatchesPattern(pokemonList[j], pattern)
{
    var lines := SplitLines(input);
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
    ValidInputImpliesMatchExists(input);
    ValidInputMatchExistsDetail(input);
    FirstMatchExists(pattern, pokemonList);
    
    var i := 0;
    while i < |pokemonList|
        invariant 0 <= i <= |pokemonList|
        invariant forall j :: 0 <= j < i ==> (|pokemonList[j]| != |pattern| || !MatchesPattern(pokemonList[j], pattern))
        invariant exists j :: i <= j < |pokemonList| && |pokemonList[j]| == |pattern| && MatchesPattern(pokemonList[j], pattern)
    {
        if |pokemonList[i]| == |pattern| && MatchesPattern(pokemonList[i], pattern) {
            result := pokemonList[i];
            assert forall j :: 0 <= j < i ==> (|pokemonList[j]| != |pattern| || !MatchesPattern(pokemonList[j], pattern));
            assert |result| == |pattern| && MatchesPattern(result, pattern);
            assert pokemonList[i] == result;
            assert IsFirstMatch(result, pattern, pokemonList);
            return;
        }
        LoopInvariantPreservation(pattern, pokemonList, i);
        i := i + 1;
    }
    
    assert false;
}
// </vc-code>

