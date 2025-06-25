pub fn Delete(line: &mut [char], l: usize, at: usize, p: usize)
    requires
        l <= line.len(),
        at + p <= l,
    ensures
        line[..at] == old(line)[..at],
        line[at..l-p] == old(line)[at+p..l],
{
}