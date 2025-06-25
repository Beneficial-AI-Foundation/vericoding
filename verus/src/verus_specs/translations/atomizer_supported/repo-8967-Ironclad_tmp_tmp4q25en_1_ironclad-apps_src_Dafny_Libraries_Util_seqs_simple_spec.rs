pub fn lemma_vacuous_statement_about_a_sequence(intseq: Seq<int>, j: int)
    requires(0 <= j < intseq.len())
    ensures(intseq.subrange(0, j) == intseq.subrange(0, j))
{
}

pub fn lemma_painful_statement_about_a_sequence(intseq: Seq<int>)
    ensures(intseq == intseq.subrange(0, intseq.len() as int))
{
}

pub fn lemma_obvious_statement_about_a_sequence(boolseq: Seq<bool>, j: int)
    requires(0 <= j < boolseq.len() - 1)
    ensures(boolseq.subrange(1, boolseq.len() as int)[j] == boolseq[j + 1])
{
}

pub fn lemma_obvious_statement_about_a_sequence_int(intseq: Seq<int>, j: int)
    requires(0 <= j < intseq.len() - 1)
    ensures(intseq.subrange(1, intseq.len() as int)[j] == intseq[j + 1])
{
}

pub fn lemma_straightforward_statement_about_a_sequence(intseq: Seq<int>, j: int)
    requires(0 <= j < intseq.len())
    ensures(intseq.subrange(0, j) + intseq.subrange(j, intseq.len() as int) == intseq)
{
}

pub fn lemma_sequence_reduction(s: Seq<int>, b: nat)
    requires(0 < b < s.len())
    ensures(s.subrange(0, b as int).subrange(0, b - 1) == s.subrange(0, b - 1))
{
}

pub fn lemma_seq_concatenation_associative(a: Seq<int>, b: Seq<int>, c: Seq<int>)
    ensures((a + b) + c == a + (b + c))
{
}

pub fn lemma_subseq_concatenation(s: Seq<int>, left: int, middle: int, right: int)
    requires(0 <= left <= middle <= right <= s.len())
    ensures(s.subrange(left, right) == s.subrange(left, middle) + s.subrange(middle, right))
{
}

pub fn lemma_seq_equality(a: Seq<int>, b: Seq<int>, len: int)
    requires(a.len() == b.len() == len)
    requires(forall|i: int| 0 <= i < len ==> a[i] == b[i])
    ensures(a == b)
{
}

pub fn lemma_seq_suffix(s: Seq<int>, prefix_length: int, index: int)
    requires(0 <= prefix_length <= index < s.len())
    ensures(s[index] == s.subrange(prefix_length, s.len() as int)[index - prefix_length])
{
}