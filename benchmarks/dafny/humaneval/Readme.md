Cleaned by:
- removing comments, and method bodies
- rename by removing "chiosa" and "jetbrains" (the "")

I haven't removed the functions in vc-helpers but moved them to vc-preamble. Please let me know if we want them removed.

Small quality checks:
- fix non-compiling code: some had `function` in vc-spec so i replaced it by `method`; some had issues with paranthesis. 

I moved 2 to problematic:
- humaneval_091.yaml - count_bored_sentences timeout
- humaneval_140.yaml - weird error
