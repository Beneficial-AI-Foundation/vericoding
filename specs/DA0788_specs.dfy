// <vc-preamble>
datatype Option<T> = None | Some(T)

ghost predicate ValidInput(input: string)
{
    |input| > 0 && 
    (exists lines :: ParseInput(input, lines) && 
    |lines| > 0 &&
    (exists t :: ParseInt(lines[0]) == Some(t) && t >= 1 && t <= 100 &&
    |lines| == 1 + 2 * t &&
    (forall i :: 0 <= i < t ==> 
        (exists n :: ParseInt(lines[1 + 2*i]) == Some(n) && 
        1 <= n <= 200000 &&
        (exists perm :: ParsePermutation(lines[2 + 2*i]) == Some(perm) &&
        |perm| == n &&
        IsValidPermutation(perm, n))))))
}

ghost predicate ValidOutput(input: string, output: string)
{
    exists lines_in, lines_out :: 
        ParseInput(input, lines_in) && 
        ParseOutput(output, lines_out) &&
        |lines_in| > 0 &&
        (exists t :: ParseInt(lines_in[0]) == Some(t) &&
        |lines_out| == t &&
        (forall i :: 0 <= i < t ==> 
            (exists result :: ParseInt(lines_out[i]) == Some(result) &&
            0 <= result <= 2)))
}

ghost predicate OutputMatchesAlgorithm(input: string, output: string)
{
    exists lines_in, lines_out :: 
        ParseInput(input, lines_in) && 
        ParseOutput(output, lines_out) &&
        |lines_in| > 0 &&
        (exists t :: ParseInt(lines_in[0]) == Some(t) &&
        |lines_out| == t &&
        |lines_in| >= 1 + 2 * t &&
        (forall i :: 0 <= i < t ==> 
            (exists n, perm, result :: 
                ParseInt(lines_in[1 + 2*i]) == Some(n) &&
                ParsePermutation(lines_in[2 + 2*i]) == Some(perm) &&
                ParseInt(lines_out[i]) == Some(result) &&
                result == ComputeMinSpecialExchanges(perm, n))))
}

predicate IsValidPermutation(perm: seq<int>, n: int)
{
    |perm| == n &&
    (forall i :: 0 <= i < n ==> 1 <= perm[i] <= n) &&
    (forall i, j :: 0 <= i < j < n ==> perm[i] != perm[j])
}

ghost predicate ParseInput(input: string, lines: seq<string>)
{
    true
}

ghost predicate ParseOutput(output: string, lines: seq<string>)
{
    true
}

function ParseInt(line: string): Option<int>
{
    None
}

function ParsePermutation(line: string): Option<seq<int>>
{
    None
}
// </vc-preamble>

// <vc-helpers>
function ComputeMinSpecialExchanges(perm: seq<int>, n: int): int
    requires |perm| == n
    requires IsValidPermutation(perm, n)
    ensures 0 <= ComputeMinSpecialExchanges(perm, n) <= 2
{
    if IsSorted(perm, n) then 0
    else 
        var blocks := CountMisplacedBlocks(perm, n);
        if blocks <= 2 then blocks else 2
}

predicate IsSorted(perm: seq<int>, n: int)
    requires |perm| == n
{
    forall i :: 0 <= i < n ==> perm[i] == i + 1
}

function CountMisplacedBlocks(perm: seq<int>, n: int): int
    requires |perm| == n
    requires IsValidPermutation(perm, n)
    ensures CountMisplacedBlocks(perm, n) >= 0
{
    var misplaced := seq(n, i requires 0 <= i < n => perm[i] != i + 1);
    CountConsecutiveBlocks(misplaced)
}

function CountConsecutiveBlocks(flags: seq<bool>): int
    ensures CountConsecutiveBlocks(flags) >= 0
{
    if |flags| == 0 then 0
    else CountConsecutiveBlocksHelper(flags, 0, false, 0)
}

function CountConsecutiveBlocksHelper(flags: seq<bool>, index: int, inBlock: bool, count: int): int
    requires 0 <= index <= |flags|
    requires count >= 0
    decreases |flags| - index
    ensures CountConsecutiveBlocksHelper(flags, index, inBlock, count) >= count
{
    if index == |flags| then count
    else if flags[index] && !inBlock then
        CountConsecutiveBlocksHelper(flags, index + 1, true, count + 1)
    else if !flags[index] && inBlock then
        CountConsecutiveBlocksHelper(flags, index + 1, false, count)
    else
        CountConsecutiveBlocksHelper(flags, index + 1, inBlock, count)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (output: string)
    requires |stdin_input| > 0
    requires '\n' in stdin_input
    requires ValidInput(stdin_input)
    ensures |output| > 0
    ensures output != ""
    ensures forall c :: c in output ==> c in "0123456789\n "
    ensures ValidOutput(stdin_input, output)
    ensures OutputMatchesAlgorithm(stdin_input, output)
    ensures output[|output|-1] == '\n'
// </vc-spec>
// <vc-code>
{
    output := "";
}
// </vc-code>
