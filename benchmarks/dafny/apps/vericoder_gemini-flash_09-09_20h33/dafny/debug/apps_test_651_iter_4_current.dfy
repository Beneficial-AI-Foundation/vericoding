predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 3 &&
    HasValidDimensions(lines) &&
    HasValidGrid(lines) &&
    HasStartAndEnd(lines) &&
    HasValidPath(lines)
}

predicate HasValidDimensions(lines: seq<string>)
    requires |lines| >= 1
{
    var dimensions := ParseTwoInts(lines[0]);
    var n := dimensions.0;
    var m := dimensions.1;
    n > 0 && m > 0 && |lines| >= n + 2
}

predicate HasValidGrid(lines: seq<string>)
    requires |lines| >= 1
{
    var dimensions := ParseTwoInts(lines[0]);
    var n := dimensions.0;
    var m := dimensions.1;
    n > 0 && m > 0 && |lines| >= n + 2 &&
    forall i :: 1 <= i <= n && i < |lines| ==>
        forall j :: 0 <= j < |lines[i]| && j < m ==>
            lines[i][j] in {'.', '#', 'S', 'E'}
}

predicate HasStartAndEnd(lines: seq<string>)
    requires |lines| >= 1
{
    var dimensions := ParseTwoInts(lines[0]);
    var n := dimensions.0;
    var m := dimensions.1;
    n > 0 && m > 0 && |lines| >= n + 2 &&
    (exists i, j :: 1 <= i <= n && i < |lines| && 0 <= j < |lines[i]| && j < m && lines[i][j] == 'S') &&
    (exists i, j :: 1 <= i <= n && i < |lines| && 0 <= j < |lines[i]| && j < m && lines[i][j] == 'E') &&
    CountOccurrences(lines, n, m, 'S') == 1 &&
    CountOccurrences(lines, n, m, 'E') == 1
}

predicate HasValidPath(lines: seq<string>)
    requires |lines| >= 1
{
    var dimensions := ParseTwoInts(lines[0]);
    var n := dimensions.0;
    var m := dimensions.1;
    n > 0 && m > 0 && |lines| >= n + 2 &&
    ValidPathString(lines[n + 1])
}

predicate ValidPathString(path: string)
{
    forall i :: 0 <= i < |path| ==> '0' <= path[i] <= '3'
}

predicate ValidResult(result: string)
{
    |result| > 0 &&
    forall c :: c in result ==> ('0' <= c <= '9') || c == '\n'
}

function CountValidWays(input: string): int
    requires ValidInput(input)
    ensures CountValidWays(input) >= 0
    ensures CountValidWays(input) <= 24
{
    var lines := SplitLines(input);
    var dimensions := ParseTwoInts(lines[0]);
    var n := dimensions.0;
    var m := dimensions.1;
    var start := FindStart(lines, n, m);
    var end := FindEnd(lines, n, m);
    var path := lines[n + 1];
    CountPermutationsReachingGoal(lines, n, m, path, start, end)
}

// <vc-helpers>
predicate {:opaque} IsDigit(c: char) { '0' <= c <= '9' }

function {:opaque} StringToInt(s: string): int
  requires forall i :: 0 <= i < |s| ==> IsDigit(s[i])
  ensures StringToInt(s) >= 0
{
  if |s| == 0 then 0 else (s[|s|-1] as int - '0' as int) + 10 * StringToInt(s[..|s|-1])
}

function SplitLines(input: string): seq<string>
{
    var lines: seq<string> := [];
    var currentLine: string := "";
    for i := 0 to |input|
        invariant 0 <= i <= |input|
        invariant forall k :: 0 <= k < |lines| ==> "\n" !in lines[k]
        invariant "\n" !in currentLine
        invariant (StringJoin(lines, "\n") + (if currentLine != "" then currentLine else "")) == input[..i] ||
                  (input == "" && i == 0 && lines == [] && currentLine == "") ||
                  (input != "" && i == 0 && lines == [] && currentLine == "") ||
                  (input != "" && i > 0 && currentLine != "" && StringJoin(lines, "\n") + currentLine == input[..i]) ||
                  (input != "" && i > 0 && currentLine == "" && StringJoin(lines, "\n") + "\n" == input[..i])
    {
        if i < |input| {
            if input[i] == '\n' {
                lines := lines + [currentLine];
                currentLine := "";
            } else {
                currentLine := currentLine + input[i];
            }
        } else {
            // After the loop, if currentLine is not empty, add it.
            // This handles the case where the input doesn't end with a newline.
            if currentLine != "" {
                lines := lines + [currentLine];
            }
        }
    }
    return lines
}

function StringJoin(lines: seq<string>, separator: string): string
    ensures separator != "" ==> forall i :: 0 <= i < |lines|-1 ==> lines[i] + separator + lines[i+1] in StringJoin(lines, separator)
{
    if |lines| == 0 then ""
    else if |lines| == 1 then lines[0]
    else lines[0] + separator + StringJoin(lines[1..], separator)
}

function StringLengthSum(lines: seq<string>): int
    reads lines
    ensures StringLengthSum(lines) >= 0
{
    if |lines| == 0 then 0
    else |lines[0]| + StringLengthSum(lines[1..]) + (|lines| -1) // +|lines|-1 for the newlines
}

function ParseTwoInts(s: string): (int, int)
    requires exists i :: 0 <= i < |s| && s[i] == ' '
    requires var parts := SplitStringToPair(s, ' ');
             (forall j :: 0 <= j < |parts.0| ==> IsDigit(parts.0[j])) &&
             (forall j :: 0 <= j < |parts.1| ==> IsDigit(parts.1[j]))
    ensures var x, y := ParseTwoInts(s); x >= 0 && y >= 0
{
    var parts := SplitStringToPair(s, ' ');
    (StringToInt(parts.0), StringToInt(parts.1))
}

function SplitStringToPair(s: string, separator: char): (string, string)
    requires exists i :: 0 <= i < |s| && s[i] == separator
    ensures var p0, p1 := SplitStringToPair(s, separator);
            |p0| + 1 + |p1| == |s|
    ensures var p0, p1 := SplitStringToPair(s, separator);
            p0 == s[..s.IndexOf(separator)] && p1 == s[s.IndexOf(separator)+1..]
{
    var index := s.IndexOf(separator);
    (s[..index], s[index+1..])
}

function SplitString(s: string, separator: char): seq<string>
    ensures forall i :: 0 <= i < |SplitString(s, separator)| ==> separator !in SplitString(s, separator)[i]
{
    var parts: seq<string> := [];
    var start := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant 0 <= start <= i
        invariant forall k :: 0 <= k < |parts| ==> separator !in parts[k]
        invariant (StringJoin(parts, separator as string) + (if start <= |s| then s[start..i] else "")) == s[..i]
    {
        if s[i] == separator
        {
            parts := parts + [s[start..i]];
            start := i + 1;
        }
        i := i + 1;
    }
    parts := parts + [s[start..i]];
    return parts
}

predicate IsDigitChar(c: char) { '0' <= c <= '9' }
predicate IsLetterChar(c: char) { ('a' <= c <= 'z') || ('A' <= c <= 'Z') }

function CountOccurrences(lines: seq<string>, n: int, m: int, target: char): int
    reads lines
    requires |lines| >= n + 2
    requires forall i :: 1 <= i <= n && i <= |lines| -1 ==> |lines[i]| >= m
    ensures CountOccurrences(lines, n, m, target) >= 0
{
    var count := 0;
    for i := 1 to n
        invariant 1 <= i <= n+1
        invariant count == (calc_occurrences_sum_upto_row(lines, n, m, target, i-1))
    {
        for j := 0 to m-1
            invariant 0 <= j <= m
            invariant count == (calc_occurrences_sum_upto_row(lines, n, m, target, i-1)) + (calc_occurrences_row_sum_upto_col(lines[i], m, target, j))
        {
            if lines[i][j] == target {
                count := count + 1;
            }
        }
    }
    count
}

function calc_occurrences_row_sum_upto_col(s: string, m: int, target: char, end_col: int): int
    requires |s| >= m
    requires 0 <= end_col <= m
{
    var sum := 0;
    for j := 0 to end_col-1
        invariant 0 <= j <= end_col
        // invariant sum == (seq(end_col, k => if s[k] == target then 1 else 0)).Sum() // This invariant is complex for Dafny to prove
    {
        if s[j] == target then sum := sum + 1;
    }
    sum
}

function calc_occurrences_sum_upto_row(lines: seq<string>, n: int, m: int, target: char, end_row: int): int
    reads lines
    requires |lines| >= n + 2
    requires forall i :: 1 <= i <= n && i <= |lines| -1 ==> |lines[i]| >= m
    requires 0 <= end_row <= n
{
    var sum := 0;
    for i := 1 to end_row
        invariant 1 <= i <= end_row+1
        // invariant sum == (seq(end_row, k => (calc_occurrences_row_sum_upto_col(lines[k+1], m, target, m)))[..]).Sum() // This invariant is complex for Dafny to prove
    {
        sum := sum + calc_occurrences_row_sum_upto_col(lines[i], m, target, m);
    }
    sum
}

function FindStart(lines: seq<string>, n: int, m: int): (int, int)
    requires HasStartAndEnd(lines)
    requires HasValidGrid(lines)
    ensures 1 <= FindStart(lines, n, m).0 <= n
    ensures 0 <= FindStart(lines, n, m).1 < m
{
    for i := 1 to n
        invariant 1 <= i <= n + 1
    {
        for j := 0 to m-1
            invariant 0 <= j <= m
        {
            if lines[i][j] == 'S' {
                return (i, j);
            }
        }
    }
    (0,0) // Should not reach here due to HasStartAndEnd
}

function FindEnd(lines: seq<string>, n: int, m: int): (int, int)
    requires HasStartAndEnd(lines)
    requires HasValidGrid(lines)
    ensures 1 <= FindEnd(lines, n, m).0 <= n
    ensures 0 <= FindEnd(lines, n, m).1 < m
{
    for i := 1 to n
        invariant 1 <= i <= n + 1
    {
        for j := 0 to m-1
            invariant 0 <= j <= m
        {
            if lines[i][j] == 'E' {
                return (i, j);
            }
        }
    }
    (0,0) // Should not reach here due to HasStartAndEnd
}

predicate IsValidPosition(x: int, y: int, n: int, m: int)
{
    1 <= x <= n && 0 <= y < m
}

predicate CanMove(lines: seq<string>, n: int, m: int, x: int, y: int, newX: int, newY: int)
    requires |lines| >= n + 2
    requires forall i :: 1 <= i <= n && i <= |lines| -1 ==> |lines[i]| >= m
    requires 1 <= x <= n && 0 <= y < m
    requires IsValidPosition(x,y,n,m)
{
    IsValidPosition(newX, newY, n, m) &&
    (lines[newX][newY] == '.' || lines[newX][newY] == 'E')
}

// Inlined `Count` function into `UniquePermutations` to avoid issues with set to seq conversion
// Inlined `In` function as it's trivial

function CountPermutationsReachingGoal(lines: seq<string>, n: int, m: int, path: string, start: (int, int), end: (int, int)): int
    requires ValidPathString(path)
    requires HasStartAndEnd(lines)
    requires HasValidGrid(lines)
    requires 1 <= start.0 <= n && 0 <= start.1 < m
    requires 1 <= end.0 <= n && 0 <= end.1 < m
    requires |lines| >= n + 2
    requires forall i :: 1 <= i <= n && i <= |lines| -1 ==> |lines[i]| >= m
    ensures 0 <= CountPermutationsReachingGoal(lines, n, m, path, start, end) <= 24
{
    var count := 0;
    var permutations: seq<seq<int>> := GeneratePermutations(path); // A permutation is a sequence of integers 0, 1, 2, 3
    for p_idx := 0 to |permutations|-1
        invariant 0 <= p_idx <= |permutations|
        invariant count >= 0
    {
        var currentPermutation := permutations[p_idx];
        var currentX := start.0;
        var currentY := start.1;
        var reachedEnd := false;
        var path_valid := true;

        for step_idx := 0 to |path|-1
            invariant 0 <= step_idx <= |path|
            invariant path_valid ==> (CanReach(lines, n, m, path, start, currentPermutation, end, step_idx, (currentX, currentY)))
             && (
            (step_idx == 0 && currentX == start.0 && currentY == start.1) ||
            (step_idx > 0 && IsValidPosition(currentX, currentY, n, m) &&
            (lines[currentX][currentY] == '.' || lines[currentX][currentY] == 'E') )
        )
        {
            var direction := currentPermutation[step_idx];
            var newX := currentX;
            var newY := currentY;

            if direction == 0 { newX := currentX - 1; } // Up
            else if direction == 1 { newX := currentX + 1; } // Down
            else if direction == 2 { newY := currentY - 1; } // Left
            else if direction == 3 { newY := currentY + 1; } // Right

            if IsValidPosition(newX, newY, n, m) && (lines[newX][newY] == '.' || lines[newX][newY] == 'E') {
                currentX := newX;
                currentY := newY;
                if (currentX, currentY) == end {
                    reachedEnd := true;
                    break; // Path found for this permutation
                }
            } else {
                path_valid := false;
                break; // Invalid move for this permutation
            }
        }
        if reachedEnd {
            count := count + 1;
        }
    }
    count
}

predicate CanReach(lines: seq<string>, n: int, m: int, path: string, start: (int, int), permutation: seq<int>, end: (int, int), k: int, currentPos: (int, int))
    requires HasValidGrid(lines)
    requires 1 <= start.0 <= n && 0 <= start.1 < m
    requires 1 <= end.0 <= n && 0 <= end.1 < m
    requires |lines| >= n + 2
    requires forall i :: 1 <= i <= n && i <= |lines| -1 ==> |lines[i]| >= m
    requires 0 <= k <= |path|
    requires forall i :: 0 <= i < |permutation| ==> 0 <= permutation[i] < 4
{
    if k == 0 then currentPos == start
    else
        var prev_pos := CalculatePosition(lines, n, m, path, start, permutation, k-1);
        var prevX := prev_pos.0;
        var prevY := prev_pos.1;
        var dir := permutation[k-1];
        var newX' := prevX;
        var newY' := prevY;
        if dir == 0 then newX' := prevX - 1
        else if dir == 1 then newX' := prevX + 1
        else if dir == 2 then newY' := prevY - 1
        else if dir == 3 then newY' := prevY + 1;

        IsValidPosition(newX', newY', n, m) &&
        (lines[newX'][newY'] == '.' || lines[newX'][newY'] == 'E') &&
        currentPos == (newX', newY')
}

function CalculatePosition(lines: seq<string>, n: int, m: int, path: string, start: (int, int), permutation: seq<int>, k: int): (int, int)
    requires HasValidGrid(lines)
    requires 1 <= start.0 <= n && 0 <= start.1 < m
    requires |lines| >= n + 2
    requires forall i :: 1 <= i <= n && i <= |lines| -1 ==> |lines[i]| >= m
    requires 0 <= k <= |path|
    requires forall i :: 0 <= i < |permutation| ==> 0 <= permutation[i] < 4
    // Path validity up to k-1 implies this function won't return an invalid position
    // (That means the path does not go out of bounds or into walls up to k-1)
    // The `CountPermutationsReachingGoal` function implicitly handles this validation.
{
    var currentX := start.0;
    var currentY := start.1;
    for i := 0 to k-1
        invariant 0 <= i <= k
        invariant (i == 0 && currentX == start.0 && currentY == start.1) || (IsValidPosition(currentX, currentY, n, m) || (currentX == start.0 && currentY == start.1))
        invariant (i == 0 && currentX == start.0 && currentY == start.1) || (IsValidPosition(currentX, currentY, n, m) || (currentX == start.0 && currentY == start.1))
        invariant forall j :: 0 <= j < i ==> IsValidPosition(CalculatePosition(lines, n, m, path, start, permutation, j+1).0, CalculatePosition(lines, n, m, path, start, permutation, j+1).1, n, m) || (CalculatePosition(lines, n, m, path, start, permutation, j+1).0 == start.0 && CalculatePosition(lines, n, m, path, start, permutation, j+1).1 == start.1)
        invariant forall j :: 0 <= j < i ==> (CanMove(lines, n, m, CalculatePosition(lines, n, m, path, start, permutation, j).0, CalculatePosition(lines, n, m, path, start, permutation, j).1, CalculatePosition(lines, n, m, path, start, permutation, j+1).0, CalculatePosition(lines, n, m, path, start, permutation, j+1).1) || (CalculatePosition(lines, n, m, path, start, permutation, j+1).0 == start.0 && CalculatePosition(lines, n, m, path, start, permutation, j+1).1 == start.1) )
    {
        var direction := permutation[i];
        if direction == 0 { currentX := currentX - 1; }
        else if direction == 1 { currentX := currentX + 1; }
        else if direction == 2 { currentY := currentY - 1; }
        else if direction == 3 { currentY := currentY + 1; }
    }
    (currentX, currentY)
}


function GeneratePermutations(path: string): seq<seq<int>>
    requires ValidPathString(path)
    ensures var p := GeneratePermutations(path);
            |p| <= 24 // Max path length 4, 4! = 24 permutations
            forall i :: 0 <= i < |p| ==> |p[i]| == |path|
            forall i :: 0 <= i < |p| ==> forall j :: 0 <= j < |p[i]| ==> IsDirection(p[i][j])
{
    var digits: seq<int> := seq(|path|, i => path[i] as int - '0' as int);
    return UniquePermutations(digits);
}

predicate IsDirection(d: int) { 0 <= d <= 3 }

function UniquePermutations(s: seq<int>): seq<seq<int>>
    requires forall i :: 0 <= i < |s| ==> IsDirection(s[i])
    ensures (|s| == 0 && UniquePermutations(s) == [[]]) ||
            (|s| == 1 && UniquePermutations(s) == [[s[0]]]) ||
            forall p :: p in UniquePermutations(s) ==> |p| == |s|
    ensures var p := UniquePermutations(s);
            forall i :: 0 <= i < |p| ==> |p[i]| == |s|
            forall i :: 0 <= i < |p| ==> forall j :: 0 <= j < |p[i]| ==> IsDirection(p[i][j])
            forall p1, p2 :: p1 in p && p2 in p && p1 == p2 ==> Count(p, p1) == 1
    ensures |s| <= 4 ==> |UniquePermutations(s)| <= 24 // 4! = 24
{
    if |s| == 0 then [[]]
    else if |s| == 1 then [[s[0]]]
    else
    (
        var result_set: set<seq<int>> := {};
        for i := 0 to |s|-1
            invariant 0 <= i <= |s|
            invariant forall e :: e in result_set ==> |e| == |s|
            invariant forall e :: e in result_set ==> forall k :: 0 <= k < |e| ==> IsDirection(e[k])
        {
            var head := s[i];
            var tail := s[..i] + s[i+1..];
            var permsOfTail := UniquePermutations(tail);
            for p_tail_idx := 0 to |permsOfTail|-1
                invariant 0 <= p_tail_idx <= |permsOfTail|
                invariant forall e :: e in result_set ==> |e| == |s|
                invariant forall e :: e in result_set ==> forall k :: 0 <= k < |e| ==> IsDirection(e[k])
            {
                result_set := result_set + [{head} + permsOfTail[p_tail_idx]];
            }
        }
        result_set.ToSeq()
    )
}

function Count<T>(s: seq<T>, e: T): int {
  var count := 0;
  for i := 0 to |s|-1 {
    if s[i] == e then count := count + 1;
  }
  count
}

function ToSeq<T>(s: set<T>): seq<T>
  ensures forall x :: x in s <==> x in ToSeq(s)
  ensures |ToSeq(s)| == |s|
{
  if s == {} then []
  else var x :| x in s; [x] + ToSeq(s - {x})
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    ensures ValidResult(result)
    ensures var numResult := StringToInt(if '\n' in result then result[..|result|-1] else result);
            0 <= numResult <= 24
    ensures ValidInput(stdin_input) ==>
            var numResult := StringToInt(if '\n' in result then result[..|result|-1] else result);
            numResult == CountValidWays(stdin_input)
    ensures !ValidInput(stdin_input) ==>
            StringToInt(if '\n' in result then result[..|result|-1] else result) == 0
// </vc-spec>
// <vc-code>
{
    var num_result: int;
    if ValidInput(stdin_input) {
        num_result := CountValidWays(stdin_input);
    } else {
        num_result := 0;
    }
    result := num_result as string + "\n";
    return result;
}
// </vc-code>

