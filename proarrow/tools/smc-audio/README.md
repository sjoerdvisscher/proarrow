# Hear an SMC program

From the repository root:

```sh
cabal run smc-audio -- /tmp/proarrow-audio
```

Play `dry.wav`, then `echo.wav`. Both contain the same short arpeggio; the second adds
repeating echoes. `echo.svg` draws the network that produces them.

The program is the feedback connection itself:

```haskell
echoWith mix delay = proc @(F a) @(F a) \input -> SMC.do
  rec output <- mix -< (input, delay -< output)
  returnA -< output
```

`mix` adds the input to half of the delayed output. `delay` stores 0.3 seconds of audio,
initially filled with silence. An output returns as an echo after 0.3 seconds, then again
after 0.6 seconds at half that amplitude, and so on. The positive delay lets the network
produce a sample before it needs that sample back.

The variables are wires. Using `output` in the feedback connection and as the result copies
it, while `rec` closes the loop. The source does not manage a buffer, shuffle a tuple or call
an arrow combinator.

`echoWith` is interpreted twice: `Arr SF` uses Yampa to process audio, and `Svg` draws the
mixer, delay and feedback wire. The implementation is shared; only the supplied boxes change.
Yampa is wrapped with `Arr`, which supplies SMC's promonad and feedback instances from
`Arrow` and `ArrowLoop`.

The executable samples five seconds at 44,100 Hz and writes mono, 16-bit PCM WAV files using
`WAVE`. Rendering is offline and needs no sound-device bindings. Yampa is a dependency of
the example and its tests; WAVE is used only by the executable. Neither is a dependency of
the main proarrow library.

The tests check an impulse's echoes against their expected amplitudes and spacing, and check
one-sample feedback against the recurrence `output[n] = input[n] + 0.5 * output[n-1]`.

The GitHub Pages documentation build also renders these files into `docs/audio/`, so the
wiki can link to [dry.wav](https://sjoerdvisscher.github.io/proarrow/audio/dry.wav) and
[echo.wav](https://sjoerdvisscher.github.io/proarrow/audio/echo.wav).
