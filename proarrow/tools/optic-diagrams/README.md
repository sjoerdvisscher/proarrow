# Optic composition by graph substitution

Render the example and a comparison page from the repository root:

```sh
python3 proarrow/tools/optic-diagrams/render.py /tmp/proarrow-optic-diagrams
```

Open `/tmp/proarrow-optic-diagrams/index.html`. The SVG files can also be viewed separately.
The diagrams come from the tested example in `test/Examples/OpticDiagrams.hs`.

The source is `g . f`. `substituteWith` expands each wire to a forward/backward pair and each
box to two legs connected by a residual. Paired boundaries connect both directions when the
encoded diagrams compose. Moving the external backward wires produces a computation from
`(a⁺, c⁻)` to `(c⁺, a⁻)`: the forward legs run `f`, then `g`, and the backward legs run `g`,
then `f`, using their own residuals. This follows §10 of Wilson and Zanasi,
[Data-Parallel Algorithms for String Diagrams](https://arxiv.org/abs/2305.01041).

The tests compare the substituted graph with an independently assembled graph and an SMC
program. The SVGs are rendered from the substituted graph through `readBack`.

The second example gives the primitives their reverse-derivative meaning for `sin(x²)`.
The square's forward leg produces `(x², x)` and the sine's produces `(sin z, cos z)`.
Their backward legs multiply the cotangent by `cos z` and then by `2x`.
The generated graph shares these residuals, with each primitive present once.

The same SMC schedule runs numerically in a writer that records primitive calls. Tests check
the chain rule, finite differences, and the existing `DIFF` implementation. The numerical computation now comes from an SMC source program in `Proarrow.Tools.Optic.OPTICS`,
with its primitives supplied by `opticLegs`. `runOptics` expands those primitives by graph
substitution, moves the backward boundaries and reads the result back with `permutations`.
The target needs only symmetric monoidal structure. Both computations are checked against
the same references.

The same module also tests parallel programs, mixed forward/backward types,
existing optic encodings, empty boundaries and multi-output primitives bound with SMC tuple
patterns. An explicit duplication optic copies a value on the forward pass and adds cotangents
on the backward pass. A writer backend checks that the compiled graph executes every leg once.
