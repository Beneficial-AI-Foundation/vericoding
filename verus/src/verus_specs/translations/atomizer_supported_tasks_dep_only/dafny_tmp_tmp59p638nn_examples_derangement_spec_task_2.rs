pub fn unknown_522(links: Seq<nat>) 
    requires(
        links.len() > 0,
        permutation(links),
        derangement(links),
        distinct(links)
    )
{
}

pub fn end(links: Seq<nat>) 
    requires(
        links.len() > 0,
        permutation(links),
        derangement(links),
        distinct(links)
    )
{
}