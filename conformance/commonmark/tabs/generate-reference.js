// Write the reference HTML of commonmark.js for each input in the given directory.
const fs = require("fs");
const path = require("path");
const c = require("commonmark");
const dir = process.argv[2];
const cases = {
  "quote-item": "> -\tfoo\n>\n>\t\tbar\n",
  "item-quote": "-\t>\tfoo\n",
  "nested-quotes": ">\t>\t\tcode\n",
  "ordered-tabs": "1.\t\tcode\n",
  "item-tab-continuation": "- a\n\n\t>\tb\n",
  "fence-in-quote": "> ```\n>\t\tx\n> ```\n",
  "item-in-item": "- a\n  -\t\tb\n",
  "quote-tab-paragraph": ">\tfoo\n>\tbar\n",
  "html-in-quote": ">\t<div>\n>\t\tx\n",
  "blank-code-in-item": "-\t\ta\n\n\t\t  b\n",
};
for (const [name, md] of Object.entries(cases)) {
  fs.writeFileSync(path.join(dir, name + ".md"), md);
  const html = new c.HtmlRenderer().render(new c.Parser().parse(md));
  fs.writeFileSync(path.join(dir, name + ".html"), html);
}
