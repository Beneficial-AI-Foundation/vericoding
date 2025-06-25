pub fn all_sequences_equal_length(sequences: Seq<Seq<int>>) -> (result: bool)
    ensures
        result <==> (forall|i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences[i].len() == sequences[j].len())
{
}