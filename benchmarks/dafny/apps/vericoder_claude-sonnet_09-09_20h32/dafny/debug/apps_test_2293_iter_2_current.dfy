predicate ValidInput(input: string)
{
    |input| > 0 && input[|input|-1] == '\n' &&
    var lines := SplitByNewlines(input);
    |lines| >= 2 && 
    var firstLineParts := SplitBySpaces(lines[0]);
    |firstLineParts| >= 2 &&
    var m := StringToInt(firstLineParts[0]);
    var n := StringToInt(firstLineParts[1]);
    m >= 1 && n >= 1 && m + 1 < |lines| &&
    forall dayIdx :: 1 <= dayIdx <= m ==> 
        var dayLine := SplitBySpaces(lines[dayIdx]);
        |dayLine| >= 1 &&
        var s := StringToInt(dayLine[0]);
        s >= 1 && s < n && s + 1 <= |dayLine| &&
        forall storeIdx :: 1 <= storeIdx <= s ==> 
            var store := StringToInt(dayLine[storeIdx]);
            1 <= store <= n
}

function ExtractDoraSet(input: string, dayIndex: int, n: int): set<int>
    requires |input| > 0
    requires dayIndex >= 0
    requires n >= 1
{
    var lines := SplitByNewlines(input);
    if dayIndex + 1 >= |lines| then {}
    else
        var dayLine := SplitBySpaces(lines[dayIndex + 1]);
        if |dayLine| <= 1 then {}
        else
            var s := StringToInt(dayLine[0]);
            if s + 1 > |dayLine| then {}
            else
                set storeIdx | 1 <= storeIdx <= s && storeIdx < |dayLine| :: StringToInt(dayLine[storeIdx])
}

function ExtractSwiperSet(input: string, dayIndex: int, n: int): set<int>
    requires |input| > 0
    requires dayIndex >= 0
    requires n >= 1
{
    var allStores := set i {:trigger} | 1 <= i <= n :: i;
    var doraSet := ExtractDoraSet(input, dayIndex, n);
    allStores - doraSet
}

predicate SolutionExists(input: string)
    requires ValidInput(input)
{
    var lines := SplitByNewlines(input);
    var firstLineParts := SplitBySpaces(lines[0]);
    var m := StringToInt(firstLineParts[0]);
    var n := StringToInt(firstLineParts[1]);
    forall i, j :: 0 <= i < m && 0 <= j < m ==> 
        !(ExtractDoraSet(input, i, n) <= ExtractSwiperSet(input, j, n))
}

// <vc-helpers>
function SplitByNewlines(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[0] == '\n' then [""] + SplitByNewlines(s[1..])
    else 
        var rest := SplitByNewlines(s[1..]);
        if |rest| == 0 then [s[0..1]]
        else [s[0..1] + rest[0]] + rest[1..]
}

function SplitBySpaces(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[0] == ' ' then [""] + SplitBySpaces(s[1..])
    else 
        var rest := SplitBySpaces(s[1..]);
        if |rest| == 0 then [s[0..1]]
        else [s[0..1] + rest[0]] + rest[1..]
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then
        if '0' <= s[0] <= '9' then s[0] as int - '0' as int
        else 0
    else
        StringToInt(s[..|s|-1]) * 10 + StringToInt(s[|s|-1..])
}

lemma DoraSetSubsetSwiper(input: string, i: int, j: int, n: int)
    requires ValidInput(input)
    requires 0 <= i < GetM(input)
    requires 0 <= j < GetM(input)
    ensures ExtractDoraSet(input, i, n) <= ExtractSwiperSet(input, j, n) <==> 
            ExtractDoraSet(input, i, n) * ExtractDoraSet(input, j, n) == {}

function GetM(input: string): int
    requires ValidInput(input)
{
    var lines := SplitByNewlines(input);
    var firstLineParts := SplitBySpaces(lines[0]);
    StringToInt(firstLineParts[0])
}

function GetN(input: string): int
    requires ValidInput(input)
{
    var lines := SplitByNewlines(input);
    var firstLineParts := SplitBySpaces(lines[0]);
    StringToInt(firstLineParts[1])
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == "possible" || result == "impossible"
    ensures result == "possible" <==> SolutionExists(input)
// </vc-spec>
// <vc-code>
{
    var lines := SplitByNewlines(input);
    var firstLineParts := SplitBySpaces(lines[0]);
    var m := StringToInt(firstLineParts[0]);
    var n := StringToInt(firstLineParts[1]);
    
    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < m ==> 
            !(ExtractDoraSet(input, ii, n) <= ExtractSwiperSet(input, jj, n))
    {
        var j := 0;
        while j < m
            invariant 0 <= j <= m
            invariant forall jj :: 0 <= jj < j ==> 
                !(ExtractDoraSet(input, i, n) <= ExtractSwiperSet(input, jj, n))
        {
            var doraSet := ExtractDoraSet(input, i, n);
            var swiperSet := ExtractSwiperSet(input, j, n);
            
            if doraSet <= swiperSet {
                return "impossible";
            }
            
            j := j + 1;
        }
        i := i + 1;
    }
    
    return "possible";
}
// </vc-code>

