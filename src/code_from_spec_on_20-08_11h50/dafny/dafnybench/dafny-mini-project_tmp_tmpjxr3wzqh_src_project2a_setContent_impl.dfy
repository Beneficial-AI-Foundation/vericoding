class Document {
    var content: string

    constructor()
        ensures content == ""
    {
        content := "";"
    }

    method setContent(c: string)
        modifies this
        ensures content == c
    {
        content := c;
    }
}