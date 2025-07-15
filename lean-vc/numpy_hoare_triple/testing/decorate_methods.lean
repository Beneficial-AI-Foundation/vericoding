/-!
{
  "name": "numpy.testing.decorate_methods",
  "category": "Decorators",
  "description": "Apply a decorator to all methods in a class matching a regular expression",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.testing.decorate_methods.html",
  "doc": "Apply a decorator to all methods in a class matching a regular expression.\n\nThe given decorator is applied to all public methods of \`cls\` that are matched by the regular expression \`testmatch\` (\`\`testmatch.search(methodname)\`\`). Methods that are private, i.e. start with an underscore, are ignored.",
  "code": "def decorate_methods(cls, decorator, testmatch=None):\n    \"\"\"\n    Apply a decorator to all methods in a class matching a regular expression.\n\n    The given decorator is applied to all public methods of \`cls\` that are\n    matched by the regular expression \`testmatch\`\n    (\`\`testmatch.search(methodname)\`\`). Methods that are private, i.e. start\n    with an underscore, are ignored.\n\n    Parameters\n    ----------\n    cls : class\n        Class whose methods to decorate.\n    decorator : function\n        Decorator to apply to methods\n    testmatch : compiled regexp or str, optional\n        The regular expression. Default value is None, in which case the\n        nose default (\`\`re.compile(r'(?:^|[\\\\b_\\\\.%s-])[Tt]est' % os.sep)\`\`)\n        is used.\n        If \`testmatch\` is a string, it is compiled to a regular expression\n        first.\n\n    \"\"\"\n    if testmatch is None:\n        testmatch = re.compile(r'(?:^|[\\\\b_\\\\.%s-])[Tt]est' % os.sep)\n    else:\n        testmatch = re.compile(testmatch)\n    cls_attr = cls.__dict__\n\n    methods = [_m for _m in cls_attr.values()\n               if hasattr(_m, '__call__')]\n    for function in methods:\n        try:\n            if hasattr(function, 'compat_func_name'):\n                funcname = function.compat_func_name\n            else:\n                funcname = function.__name__\n        except AttributeError:\n            # not a function\n            continue\n        if testmatch.search(funcname) and not funcname.startswith('_'):\n            setattr(cls, funcname, decorator(function))\n    return"
}
-/

-- TODO: Implement decorate_methods
