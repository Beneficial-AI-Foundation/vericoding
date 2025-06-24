static lemma lemma_vacuous_statement_about_a_sequence(intseq:seq<int>, j:int)
    requires 0<=j<|intseq|;
    ensures intseq[0..j]==intseq[..j];
{
    // This is trivially true by definition of sequence slicing
}

static lemma lemma_painful_statement_about_a_sequence(intseq:seq<int>)
    ensures intseq==intseq[..|intseq|];
{
    // This is trivially true by definition of sequence slicing
}

static lemma lemma_obvious_statement_about_a_sequence(boolseq:seq<bool>, j:int)
    requires 0<=j<|boolseq|-1;
    ensures boolseq[1..][j] == boolseq[j+1];
{
    // This follows from the definition of sequence slicing
}

static lemma lemma_obvious_statement_about_a_sequence_int(intseq:seq<int>, j:int)
    requires 0<=j<|intseq|-1;
    ensures intseq[1..][j] == intseq[j+1];
{
    // This follows from the definition of sequence slicing
}

static lemma lemma_straightforward_statement_about_a_sequence(intseq:seq<int>, j:int)
    requires 0<=j<|intseq|;
    ensures intseq[..j] + intseq[j..] == intseq;
{
    // This is a fundamental property of sequence concatenation
}

static lemma lemma_sequence_reduction(s:seq<int>, b:nat)
    requires 0<b<|s|;
    ensures s[0..b][0..b-1] == s[0..b-1];
{
    var t := s[0..b];
    forall (i | 0<=i<b-1)
        ensures s[0..b][0..b-1][i] == s[0..b-1][i];
    {
        // The assertion follows from properties of sequence slicing
    }
}

static lemma lemma_seq_concatenation_associative(a:seq<int>, b:seq<int>, c:seq<int>)
    ensures (a+b)+c == a+(b+c);
{
    // Sequence concatenation is associative by definition
}

static lemma lemma_subseq_concatenation(s: seq<int>, left: int, middle: int, right: int)
    requires 0 <= left <= middle <= right <= |s|;
    ensures s[left..right] == s[left..middle] + s[middle..right];
{
    // This is a fundamental property of sequence slicing and concatenation
}

static lemma lemma_seq_equality(a:seq<int>, b:seq<int>, len:int)
    requires |a| == |b| == len;
    requires forall i {:trigger a[i]}{:trigger b[i]} :: 0 <= i < len ==> a[i] == b[i];
    ensures a == b;
{
    // If two sequences have the same length and all corresponding elements are equal,
    // then the sequences are equal
}

static lemma lemma_seq_suffix(s: seq<int>, prefix_length: int, index: int)
    requires 0 <= prefix_length <= index < |s|;
    ensures s[index] == s[prefix_length..][index - prefix_length];
{
    // This follows from the definition of sequence slicing
}