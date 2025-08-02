#import "@preview/bullseye:0.1.0": *
#import "@preview/diagraph:0.3.5"
#import "@preview/theorion:0.4.0"


// Custom corollary that is at the same counter depth as theorems etc.
#let (
  _corollary-counter,
  _corollary-box,
  _corollary,
  _show-corollary,
) = theorion.make-frame(
  "corollary",
  theorion.theorion-i18n-map.at("corollary"),
  counter: theorion.theorem-counter,
  render: theorion.render-fn,
)

#let init-whiteprint(body) = {
  // Set up theorion
  show: theorion.show-theorion
  show: _show-corollary
  theorion.set-inherited-levels(1)

  // Basic styling
  set par(justify: true)
  set heading(
    numbering: "1.1",
    supplement: it => if it.depth == 1 [Chapter] else [Section],
  )
  show link: set text(fill: blue.darken(20%))

  // HTML export
  show math.equation.where(block: true): show-target(html: html.frame)
  show math.equation.where(block: false): show-target(html: it => html.elem(
    "span",
    html.frame(it),
  ))

  body
}

#let _elem-fns = (
  "definition": theorion.definition,
  "theorem": theorion.theorem,
  "lemma": theorion.lemma,
  "corollary": _corollary,
)

#let _elem(
  kind: none,
  title: none,
  lean: none,
  uses: (),
  statement,
  ..args,
) = {
  assert(type(kind) == str)
  assert(type(lean) == label)
  assert(type(uses) == array)
  for use in uses { assert(type(use) == label) }

  assert(args.pos().len() <= 1)
  let proof = args.pos().at(0, default: none)

  context [
    #metadata((
      kind: kind,
      title: title,
      lean: str(lean),
      uses: uses.map(str),
    )) <whiteprint-metadata>
    #_elem-fns.at(kind)(
      title: if title == none { "" } else { title },
      statement,
    ) #lean
    #if proof != none { theorion.proof(proof) }
  ]
}

#let definition = _elem.with(kind: "definition")
#let theorem = _elem.with(kind: "theorem")
#let lemma = _elem.with(kind: "lemma")
#let corollary = _elem.with(kind: "corollary")
