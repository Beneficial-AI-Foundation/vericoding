HTML Element Generator
In this kata, you will be creating a python function that will take arguments and turn them into an HTML element.
An HTML tag has three parts:

The opening tag, which consists of a tag name and potentially attributes, all in between angle brackets.
The element content, which is the data that is shown on the webpage.  This is in between the opening and closing tags.
And the closing tag, which is an opening angle bracket, a forward slash, the name of the tag, and a closing angle bracket

If you were to have multiple attributes, they would each appear with a single space separating them

Some tags do not require a closing tag.  These are called self-closing tags.  For this kata, any tag passed into the function without 'element content' (keyword arguments) will be treated in this way:  after the tag name (and any attributes), there will be a space and then a forward slash.  See the picture to the right.

Data will be passed into the html function as such: 

The first argument will be the tag name
Any other non-keyword arguments will be element content. If no element content is given, the return value will be expected to be a self-closing tag.  If more than one argument is given as element content, you will return multiple of the same element, just with different element content, separated by one or more newline characters.
Ex: 

<p class="paragraph-text" id="example">Hello World!</p>\n<p class="paragraph-text" id="example">This is HTML code!</p>

IMPORTANT:  Because class is a python keyword, and class is a very important HTML attribute, you will also have to implement a keyword argument named cls, as opposed to class.  This attribute will appear as class="variable" in the return value of your function
Any other keyword arguments of the function will be treated as attributes of the element.  The keyword is the attribute name (left of the equals sign), and the keyword's value is the attribute's value (right of the equals sign).
Element attributes will appear in the return value of your function in the order that they appear in the function's arguments when it is called.  If cls is an argument of the function, it will always appear first (before any other keyword arguments).
Several Examples are provided

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
