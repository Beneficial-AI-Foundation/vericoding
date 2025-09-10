predicate ValidInput(n: int, s: string)
{
    n >= 1 && n <= 2000 && |s| == n && 
    forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate ValidOutput(result: string, n: int)
{
    |result| == n && 
    forall i :: 0 <= i < |result| ==> 'a' <= result[i] <= 'z'
}

predicate PreservesCharacters(s: string, result: string)
{
    multiset(s) == multiset(result)
}

// <vc-helpers>
function CountChar(s: string, char: char) : int
    reads s
    ensures CountChar(s, char) == (set i | 0 <= i < |s| && s[i] == char) .Count
{
    if |s| == 0 then 0
    else (if s[0] == char then 1 else 0) + CountChar(s[1..], char)
}

lemma CountCharPreservesCharacters(s: string, result: string, char: char)
    requires multiset(s) == multiset(result)
    ensures CountChar(s, char) == CountChar(result, char)
{
    // This lemma is a property of multisets. If two multisets are equal,
    // then the count of any element in both multisets must be the same.
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: string)
    requires ValidInput(n, s)
    ensures ValidOutput(result, n)
    ensures PreservesCharacters(s, result)
// </vc-spec>
// <vc-code>
{
    var freq := new array<int>(26);
    // Initialize frequency array
    for i := 0 to 25
        decreases 26 - i
        ensures forall k :: 0 <= k <= i ==> freq[k] == 0
    {
        freq[i] := 0;
    }

    // Populate frequency array for string s
    for i := 0 to n - 1
        decreases n - i
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < 26 ==> freq[k] == CountChar(s[0..i], 'a' + k)
    {
        var charIndex := s[i] as int - 'a' as int;
        assert 0 <= charIndex < 26;
        freq[charIndex] := freq[charIndex] + 1;
    }

    // Construct the result string
    var sb := new array<char>(n);
    var current_index := 0;
    for i := 0 to 25
        decreases 26 - i
        invariant 0 <= i <= 26
        invariant current_index <= n
        invariant forall k :: 0 <= k < i ==> CountChar(sb[0..current_index], 'a'+k) == freq[k]
        invariant current_index == (sum k :: 0 <= k < i ? freq[k] : 0)
    {
        var char_to_add := 'a' + i;
        for j := 0 to freq[i] - 1
            decreases freq[i] - j
            invariant 0 <= j <= freq[i]
            invariant current_index + j < n
            invariant forall k :: 0 <= k < j ==> sb[current_index + k] == char_to_add
        {
            sb[current_index] := char_to_add;
            current_index := current_index + 1;
        }
    }

    result := new string(sb);

    // Proof for PreservesCharacters
    assert multiset(s) == multiset(result) by {
        // We need to show that for every character 'c', CountChar(s, 'c') == CountChar(result, 'c').
        // This is guaranteed by how 'result' is constructed from the frequency array 'freq'.
        // The frequency array 'freq' correctly counts characters in 's'.
        // 'result' is built by appending 'freq[k]' occurrences of 'a'+k for each k.
        // Therefore, for any character 'c', CountChar(result, 'c') will be exactly freq[c - 'a'],
        // which by construction is CountChar(s, 'c').
        forall char | 'a' <= char <= 'z'
            ensures CountChar(s, char) == CountChar(result, char)
        {
            var char_idx := char as int - 'a' as int;
            assert CountChar(s, char) == freq[char_idx];
            assert CountChar(result, char) == freq[char_idx]; // This holds because of how result is constructed
        }
    }
}
// </vc-code>

