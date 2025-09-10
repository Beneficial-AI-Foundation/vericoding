predicate ValidInput(n: int, k: int, a: int, m: int, shots: seq<int>)
{
    n > 0 && k > 0 && a > 0 && m > 0 && |shots| == m &&
    (forall i :: 0 <= i < |shots| ==> 1 <= shots[i] <= n)
}

function canPlaceShipsFunc(n: int, k: int, a: int, shots: seq<int>, numShots: int): bool
    requires n > 0 && k > 0 && a > 0 && numShots >= 0
    requires numShots <= |shots|
    requires forall i :: 0 <= i < |shots| ==> 1 <= shots[i] <= n
{
    var hitCells := set i | 0 <= i < numShots && i < |shots| :: shots[i];
    greedyShipPlacement(n, k, a, hitCells) >= k
}

function greedyShipPlacement(n: int, k: int, a: int, hitCells: set<int>): int
    requires n > 0 && k > 0 && a > 0
    requires forall cell :: cell in hitCells ==> 1 <= cell <= n
{
    greedyPlaceShipsFromPosition(1, n, k, a, hitCells)
}

function greedyPlaceShipsFromPosition(pos: int, n: int, k: int, a: int, hitCells: set<int>): int
    requires pos >= 1 && n > 0 && k >= 0 && a > 0
    requires forall cell :: cell in hitCells ==> 1 <= cell <= n
    decreases n - pos + 1, k
{
    if pos > n || k == 0 then 0
    else if pos + a - 1 <= n && forall cell :: pos <= cell <= pos + a - 1 ==> cell !in hitCells then
        1 + greedyPlaceShipsFromPosition(pos + a + 1, n, k - 1, a, hitCells)
    else
        greedyPlaceShipsFromPosition(pos + 1, n, k, a, hitCells)
}

predicate isNaturalNumberString(str: string)
{
    |str| > 0 && str[0] != '0' && forall i :: 0 <= i < |str| ==> '0' <= str[i] <= '9'
}

function parseInputSpec(input: string): seq<string>
    requires |input| > 0
    ensures |parseInputSpec(input)| >= 0
{
    []
}

function parseThreeIntsSpec(line: string): (int, int, int)
    ensures parseThreeIntsSpec(line).0 > 0 && parseThreeIntsSpec(line).1 > 0 && parseThreeIntsSpec(line).2 > 0
{
    (1, 1, 1)
}

function parseIntSpec(line: string): int
    ensures parseIntSpec(line) >= 0
{
    0
}

function parseIntArraySpec(line: string): seq<int>
    ensures forall i :: 0 <= i < |parseIntArraySpec(line)| ==> parseIntArraySpec(line)[i] > 0
{
    []
}

function intToStringSpec(value: int): string
    requires value >= 1
    ensures |intToStringSpec(value)| > 0
    ensures isNaturalNumberString(intToStringSpec(value))
{
    "1"
}

// <vc-helpers>
lemma canPlaceShipsMonotonic(n: int, k: int, a: int, shots: seq<int>, i: int, j: int)
    requires n > 0 && k > 0 && a > 0
    requires forall idx :: 0 <= idx < |shots| ==> 1 <= shots[idx] <= n
    requires 0 <= i <= j <= |shots|
    ensures canPlaceShipsFunc(n, k, a, shots, j) ==> canPlaceShipsFunc(n, k, a, shots, i)
{
    if canPlaceShipsFunc(n, k, a, shots, j) {
        var hitCellsI := set idx | 0 <= idx < i && idx < |shots| :: shots[idx];
        var hitCellsJ := set idx | 0 <= idx < j && idx < |shots| :: shots[idx];
        assert hitCellsI <= hitCellsJ;
        greedyPlacementMonotonic(n, k, a, hitCellsI, hitCellsJ);
    }
}

lemma greedyPlacementMonotonic(n: int, k: int, a: int, smaller: set<int>, larger: set<int>)
    requires n > 0 && k > 0 && a > 0
    requires forall cell :: cell in smaller ==> 1 <= cell <= n
    requires forall cell :: cell in larger ==> 1 <= cell <= n
    requires smaller <= larger
    ensures greedyShipPlacement(n, k, a, larger) <= greedyShipPlacement(n, k, a, smaller)
{
    greedyPlacementMonotonicFromPos(1, n, k, a, smaller, larger);
}

lemma greedyPlacementMonotonicFromPos(pos: int, n: int, k: int, a: int, smaller: set<int>, larger: set<int>)
    requires pos >= 1 && n > 0 && k >= 0 && a > 0
    requires forall cell :: cell in smaller ==> 1 <= cell <= n
    requires forall cell :: cell in larger ==> 1 <= cell <= n
    requires smaller <= larger
    ensures greedyPlaceShipsFromPosition(pos, n, k, a, larger) <= greedyPlaceShipsFromPosition(pos, n, k, a, smaller)
    decreases n - pos + 1, k
{
    if pos > n || k == 0 {
    } else {
        var canPlaceInSmaller := pos + a - 1 <= n && forall cell :: pos <= cell <= pos + a - 1 ==> cell !in smaller;
        var canPlaceInLarger := pos + a - 1 <= n && forall cell :: pos <= cell <= pos + a - 1 ==> cell !in larger;
        
        if canPlaceInSmaller && canPlaceInLarger {
            greedyPlacementMonotonicFromPos(pos + a + 1, n, k - 1, a, smaller, larger);
        } else if canPlaceInSmaller && !canPlaceInLarger {
            greedyPlacementMonotonicFromPos(pos + 1, n, k, a, smaller, larger);
        } else {
            greedyPlacementMonotonicFromPos(pos + 1, n, k, a, smaller, larger);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires stdin_input[|stdin_input|-1] == '\n'
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures result == "-1\n" || (exists shot_num_str :: |shot_num_str| > 0 && result == shot_num_str + "\n" && isNaturalNumberString(shot_num_str))
    ensures var lines := parseInputSpec(stdin_input);
            if |lines| >= 3 then
                var firstLine := parseThreeIntsSpec(lines[0]);
                var n, k, a := firstLine.0, firstLine.1, firstLine.2;
                var m := parseIntSpec(lines[1]);
                var shots := parseIntArraySpec(lines[2]);
                if ValidInput(n, k, a, m, shots) then
                    if canPlaceShipsFunc(n, k, a, shots, m) then
                        result == "-1\n"
                    else
                        exists shot_idx :: 1 <= shot_idx <= m && 
                                         result == intToStringSpec(shot_idx) + "\n" &&
                                         !canPlaceShipsFunc(n, k, a, shots, shot_idx) &&
                                         (shot_idx == 1 || canPlaceShipsFunc(n, k, a, shots, shot_idx-1))
                else
                    true
            else
                true
// </vc-spec>
// <vc-code>
{
    var lines := parseInputSpec(stdin_input);
    if |lines| < 3 {
        return "-1\n";
    }
    
    var firstLine := parseThreeIntsSpec(lines[0]);
    var n, k, a := firstLine.0, firstLine.1, firstLine.2;
    var m := parseIntSpec(lines[1]);
    var shots := parseIntArraySpec(lines[2]);
    
    if !ValidInput(n, k, a, m, shots) {
        return "-1\n";
    }
    
    if canPlaceShipsFunc(n, k, a, shots, m) {
        return "-1\n";
    }
    
    var left := 1;
    var right := m;
    var answer := m;
    
    while left <= right
        invariant 1 <= left <= right + 1 <= m + 1
        invariant left <= answer <= m
        invariant !canPlaceShipsFunc(n, k, a, shots, answer)
        invariant answer == 1 || canPlaceShipsFunc(n, k, a, shots, answer - 1)
        invariant forall i :: 1 <= i < left ==> canPlaceShipsFunc(n, k, a, shots, i)
        invariant forall i :: right < i <= m ==> !canPlaceShipsFunc(n, k, a, shots, i)
    {
        var mid := (left + right) / 2;
        
        if canPlaceShipsFunc(n, k, a, shots, mid) {
            canPlaceShipsMonotonic(n, k, a, shots, left, mid);
            left := mid + 1;
        } else {
            answer := mid;
            right := mid - 1;
        }
    }
    
    return intToStringSpec(answer) + "\n";
}
// </vc-code>

