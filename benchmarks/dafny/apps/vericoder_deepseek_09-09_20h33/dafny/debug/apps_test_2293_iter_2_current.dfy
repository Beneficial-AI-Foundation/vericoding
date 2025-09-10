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
    else
        var firstNewline := -1;
        var i := 0;
        while i < |s| && firstNewline == -1
            invariant 0 <= i <= |s|
            invariant firstNewline == -1 ==> forall k :: 0 <= k < i ==> s[k] != '\n'
            invariant firstNewline != -1 ==> 0 <= firstNewline < |s| && s[firstNewline] == '\n'
        {
            if s[i] == '\n' {
                firstNewline := i;
            }
            i := i + 1;
        }
        
        if firstNewline == -1 then [s]
        else [s[0..firstNewline]] + SplitByNewlines(s[firstNewline+1..])
}

function SplitBySpaces(s: string): seq<string>
{
    if |s| == 0 then []
    else
        var firstSpace := -1;
        var i := 0;
        while i < |s| && firstSpace == -1
            invariant 0 <= i <= |s|
            invariant firstSpace == -1 ==> forall k :: 0 <= k < i ==> s[k] != ' '
            invariant firstSpace != -1 ==> 0 <= firstSpace < |s| && s[firstSpace] == ' '
        {
            if s[i] == ' ' {
                firstSpace := i;
            }
            i := i + 1;
        }
        
        if firstSpace == -1 then [s]
        else [s[0..firstSpace]] + SplitBySpaces(s[firstSpace+1..])
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else StringToInt(s[0..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

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
    var allStores := set i | 1 <= i <= n;
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

lemma Lemma_SetDifferenceProperties<T>(s: set<T>, t: set<T>)
    ensures s <= t <==> (s - t == {})
{
}

lemma Lemma_SubsetTransitive<T>(a: set<T>, b: set<T>, c: set<T>)
    requires a <= b && b <= c
    ensures a <= c
{
}

lemma Lemma_SubsetReflexive<T>(s: set<T>)
    ensures s <= s
{
}

lemma Lemma_SubsetDifference<T>(s: set<T>, t: set<T>)
    ensures s - t <= s
{
}

lemma Lemma_SetEquivalence<T>(s: set<T>, t: set<T>)
    ensures s == t <==> (s <= t && t <= s)
{
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
    {
        var j := 0;
        while j < m
            invariant 0 <= j <= m
        {
            var doraSet := ExtractDoraSet(input, i, n);
            var swiperSet := ExtractSwiperSet(input, j, n);
            if doraSet <= swiperSet {
                result := "impossible";
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := "possible";
}
// </vc-code>

