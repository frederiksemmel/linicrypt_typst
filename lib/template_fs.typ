#import "@preview/ctheorems:1.1.0": *

#let script-size = 8pt
#let footnote-size = 8.5pt
#let small-size = 9pt
#let normal-size = 10pt
#let large-size = 12pt
#let title-size = 14pt

// This function gets your whole document as its `body` and formats
// it as an article in the style of the American Mathematical Society.
#let fs-article(
  // The article's title.
  title: [Paper title],
  // An array of authors. For each author you can specify a name,
  // department, organization, location, and email. Everything but
  // but the name is optional.
  authors: (),
  // Your article's abstract. Can be omitted if you don't have one.
  abstract: none,
  // The article's paper size. Also affects the margins.
  paper-size: "us-letter",
  // The path to a bibliography file if you want to cite some external
  // works.
  bibliography-file: none,
  // The document's content.
  body,
) = {
  // Formats the author's names in a list with commas and a
  // final "and".
  let names = authors.map(author => author.name)
  let author-string = if authors.len() == 2 {
    names.join(" and ")
  } else {
    names.join(", ", last: ", and ")
  }

  // Set document metadata.
  set document(title: title, author: names)

  // Set the body font. AMS uses the LaTeX font.
  set text(size: normal-size, font: "New Computer Modern")

  // Configure the page.
  set page(
    paper: paper-size,
    // The margins depend on the paper size.
    margin: {
      (top: 10em, left: 8em, right: 8em, bottom: 8em)
    },
    // On the first page, the footer should contain the page number.
    footer-descent: 12pt, footer: locate(loc => {
      let i = counter(page).at(loc).first()
      align(center, text(size: script-size, [#i]))
    }),
  )
  set par(justify: true)

  // Configure headings.
  set heading(numbering: "1.")
  show heading: it => {
    // Create the heading numbering.
    let number = if it.numbering != none {
      counter(heading).display(it.numbering)
      h(7pt, weak: true)
    }

    // Level 1 headings are centered and smallcaps.
    // The other ones are run-in.
    set text(size: normal-size, weight: 400)
    if it.level == 1 {
      set align(center)
      set text(size: large-size, weight: 700)
      smallcaps[
        #v(25pt, weak: true)
        #number
        #it.body
        #v(large-size, weak: true)
      ]
      counter(figure.where(kind: "theorem")).update(0)
    } else {
      v(21pt, weak: true)
      number
      let styled = if it.level == 2 { strong } else { emph }
      styled(it.body + [. ])
      h(17pt, weak: true)
    }
  }
  // show heading: it => {
  //   // Create the heading numbering.
  //   let number = if it.numbering != none {
  //     counter(heading).display(it.numbering)
  //     h(7pt, weak: true)
  //   }

  //   // Level 1 headings are centered and smallcaps.
  //   // The other ones are run-in.
  //   // set text(size: normal-size, weight: 400)
  //   if it.level == 1 {
  //     // set text(size: large-size)
  //     [
  //       #v(15pt, weak: true)
  //       #number
  //       #it.body
  //       #v(normal-size, weak: true)
  //     ]
  //     counter(figure.where(kind: "theorem")).update(0)
  //   } else {
  //     v(11pt, weak: true)
  //     number
  //     let styled = if it.level == 2 { strong } else { emph }
  //     styled(it.body + [. ])
  //     h(7pt, weak: true)
  //   }
  // }

  // Configure lists and links.
  // set list(indent: 24pt, body-indent: 5pt)
  // set enum(indent: 24pt, body-indent: 5pt)
  show link: set text(font: "New Computer Modern Mono")
  // show link: set text(font: "New Computer Modern")

  // Configure equations.
  // show math.equation: set block(below: 8pt, above: 9pt)
  // show math.equation: set text(weight: 400)

  // Configure citation and bibliography styles.
  set bibliography(style: "springer-mathphys", title: [References])

  // Theorem setup
  show: thmrules

  // Setup equations and math stuff
  set math.mat(delim: "[")
  set math.equation(numbering: "(1)")

  // Display the title and authors.
  v(35pt, weak: true)
  align(center, {
    upper(text(size: large-size, weight: 700, title))
    v(25pt, weak: true)
    upper(text(size: footnote-size, author-string))
    v(15pt, weak: true)
    text(size: footnote-size, datetime.today().display("[day] [month repr:long] [year]"))
  })

  // Display the abstract
  if abstract != none {
    v(20pt, weak: true)
    set text(script-size)
    show: pad.with(x: 35pt)
    smallcaps[Abstract. ]
    abstract
  }

  // Display the article's contents.
  v(29pt, weak: true)
  body

  // Display the bibliography, if any is given.
  if bibliography-file != none {
    show bibliography: set text(8.5pt)
    show bibliography: pad.with(x: 0.5pt)
    pagebreak()
    bibliography(bibliography-file)
  }

  // The thing ends with details about the authors.
  show: pad.with(x: 11.5pt)
  set par(first-line-indent: 0pt)
  set text(8pt)

  for author in authors {
    let keys = ("department", "organization", "location")

    let dept-str = keys
    .filter(key => key in author)
    .map(key => author.at(key))
    .join(", ")

    smallcaps(dept-str)
    linebreak()

    if "email" in author [
      _Email address:_ #link("mailto:" + author.email) \
    ]

    if "url" in author [
      _URL:_ #link(author.url)
    ]

    v(12pt, weak: true)
  }
}

// concrete theroem setup
#let theorem = thmbox("theorem", "Theorem")

#let conjecture = thmbox("conjecture", "Conjeture")

#let idea = thmbox("idea", "Idea")

#let lemma = thmbox("lemma", "Lemma")

#let proposition = thmbox("proposition", "Proposition")

#let corollary = thmbox("corollary", "Corollary")

#let definition = thmbox("definition", "Definition", inset: (x: 0em, top: 0.2em, bottom: 0.8em))

#let example = thmplain("example", "Example").with(numbering: "none")

#let remark = thmplain("remark", "Remark")

#let proof = thmplain("proof", "Proof", base: "theorem", bodyfmt: body => [#body #h(1fr) $square$ #v(2em)]).with(numbering: none)

#let sketch = thmplain(
  "sketch", "Proof Sketch", base: "theorem", bodyfmt: body => [#body #h(1fr) $square$ #v(2em)],
).with(numbering: none)
