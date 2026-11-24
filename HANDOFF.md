# Handoff: per-image association on the Hellinger cascade's own models

Written 2026-11-24 on the thesis workstation for a Claude Code session on the GPU server.

This repository is public. Keep this file and every commit here free of server paths, host names, user names, and the name of the venue or of the private paper repository.

## 1. Goal

The thesis and the paper use two cascading randomizations on purpose:

- the **attribution cascade** benchmarks attribution methods (map similarity at the cascade endpoint);
- the **Hellinger cascade** relates trajectory laws to maps (Hellinger curves, per-image association, double-random reference).

Both stay as they are. What must hold is that **inside the Hellinger cascade, the Hellinger distance and the attribution maps are computed on the same randomized models and for the same target**. Today this holds only in a 200-image control. The task is to run that control on the full 565-image test split for all three models and to rebuild the per-image association table from it.

## 2. What is wrong today

All paths are relative to the code repository (`Playing_The_Network_Backward_Official_Repository`, also the `code/` folder of the private paper repository).

The per-image association table is built by `reproduce/diagnostic_figures.py::per_image_corr_rows`. It correlates, per image,

- Hellinger distances from the Hellinger cascade (`experiments/hellinger_randomization`), with
- map similarities from the **attribution** cascade (`experiments/sanity_check_randomization`).

These two runs do not share randomized models:

1. On ViT-B/16 they randomize different layers. `ALIGNED_STEPS` joins the Hellinger step `encoder_layer_11.self_attention.out_proj` (4 randomized layers; query, key and value stay pretrained, because the packed `in_proj` of `nn.MultiheadAttention` is not an `nn.Linear`) with the map step `encoder_layer_11.self_attention.q_proj` (7 randomized layers; the attribution cascade decomposes attention first).
2. On all three models the random weights differ: both scripts draw from the global RNG in different order.
3. The targets differ: predicted class in the Hellinger cascade, dataset label in the attribution cascade.

Affected artifact: `tables/generated/per_image_corr_tabular.tex` and the macros `\perImageCrossMax`, `\perImageN` in `tables/generated/diagnostic_numbers.tex` (thesis: Table "Per-image Spearman rank correlations" in Section 7.3.2).

Not affected: the Hellinger cascade plot, the double-random reference, the map-similarity table of the attribution cascade, the input-noise experiment.

## 3. What exists already

`reproduce/control_diagnostics.py --mode paired` (with `reproduce/control_common.py`) already does the right thing: for each condition it builds one randomized model with a deterministic seed per parameter tensor, and computes on that same model object

- the Hellinger distance for both games, plain and survival-conditioned, with survival masses;
- Gradient and RG-anchor maps with their similarity to the pretrained model's maps (`spearman_abs`, `hog_pearson`);
- the target probability; and it checks state hashes.

It uses the Hellinger cascade's convention (query, key and value pretrained) and the dataset label as target. Conditions: `identity`, `head`, `aligned` (VGG-16 `features.26`, ResNet-50 `layer4.1.conv3`, ViT-B/16 `encoder_layer_11.self_attention.out_proj`), `endpoint`.

So far it was run for ViT-B/16 on a seeded subset of 200 test images (`results_summary/controls/corrected_vit_randomization.json`). Reference values:

| Condition | H (SG) | H (RG) | Gradient map ρ | RG anchor map ρ |
|---|---|---|---|---|
| Head only | 0.7552 | 0.7692 | 0.6576 | 1.0000 |
| Through block-11 output projection | 0.8856 | 0.9151 | 0.6549 | 1.0000 |
| Endpoint | 0.9505 | 0.9627 | −0.0353 | 0.3770 |

## 4. What to run

1. **Full test split, three models.** Run `python -m reproduce.control_diagnostics --mode paired --split test --seed 42 --no-faithfulness` for `--model vit_b16`, `vgg16` and `resnet50` on all 565 test images. `--subset` defaults to a random 200; pass a value that selects all images (check `control_common.sample_indices`). Use `--shard` / `--shards` for array jobs.
2. **Regression check first.** For ViT-B/16, the records of the 200 control images must reproduce the table in Section 3 to four decimals. If they do not, stop and report.
3. **Identity check.** In the `identity` condition every distance is 0 and every map similarity is 1.
4. **Survival conditioning.** Report, per model, game and condition, how many survival-conditioned distances are undefined. The script evaluates one image at a time, so an undefined value cannot remove other images.
5. **Prediction audit.** Top-1 accuracy and mean target probability per model and condition (`reproduce/control_prediction_performance.py`).

Optional, only if cheap: the same measurement at every step of the Hellinger cascade for ViT-B/16, so that map-similarity curves can be drawn next to the Hellinger curves.

## 5. Tables to generate

Generalize `reproduce/control_randomization_tables.py`, which is hard-coded to ViT-B/16 and `n = 200`:

1. **Per-image association table** in the layout of the current `per_image_corr_tabular.tex`, from the `aligned` condition of each model: the 8×8 Spearman matrix across images of H (RG, plain), H (RG, surv), H (SG, plain), H (SG, surv), Gradient `spearman_abs`, Gradient `hog_pearson`, RG-anchor `spearman_abs`, RG-anchor `hog_pearson`. Add bootstrap 95% intervals (10,000 resamples) for the distance-versus-map block to the summary JSON, and regenerate `\perImageCrossMax` and `\perImageN`.
2. **Matched-model table** for all three models on 565 images: per condition top-1 accuracy, mean target probability, the four distances, the two map similarities (mean ± standard deviation over images), and the per-image association of H (RG) with the RG-anchor map similarity with its interval.

`reproduce/diagnostic_figures.py` should take the per-image table from these records and no longer from `ALIGNED_STEPS`.

## 6. Outputs

In the code repository under `results_summary/controls/matched_cascade_full/`:

- `<model>/per_image.csv.gz`: one row per image and condition with the four distances, both survival masses, the map similarities, target, target probabilities, and state hashes.
- `summary.json`: the numbers of Section 5 with intervals, the protocol (seed, conditions, changed parameters, code commit, library versions) and the counts of undefined survival-conditioned distances.
- `tables/`: the generated TeX files and macros.
- `REPORT.md`: what ran, deviations, and every number currently quoted in the two manuscripts next to its new value.

Commit only summaries and generated TeX. No maps, datasets, weights, caches or cluster files.

## 7. Where the results go afterwards

Do not edit the thesis repository on the server: the workstation has uncommitted edits under `tex/`. Deliver through the code repository.

| Target | Files to replace |
|---|---|
| Thesis | `tex/tables/ptnb_v2/generated/per_image_corr_tabular.tex`, the two macros in `tex/tables/ptnb_v2/generated/diagnostic_numbers.tex`, `tex/tables/rebuttal/corrected_vit_randomization_tabular.tex` |
| Paper (private repository; the user gives you its location; follow its own cluster and anonymity rules; generated files and a results report only, no prose) | `tables/generated/per_image_corr_tabular.tex`, `tables/generated/diagnostic_numbers.tex`, the two `corrected_vit_*` tables |

Prose that quotes these numbers and that the authors update afterwards:

- Thesis: Section 7.1 (matched-model paragraph and table), Section 7.3.2 (protocol and interpretation of the per-image association).
- Paper: the randomization section and the randomization appendix.
