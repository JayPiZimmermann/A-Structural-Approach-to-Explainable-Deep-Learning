# Handoff: rerun the parameter-randomization diagnostics on one shared cascade

Written 2026-11-24 on the thesis workstation for a Claude Code session on the GPU server.

This repository is public. Keep this file and every commit here free of server paths, host names, user names, and the name of the venue or of the private paper repository.

## 1. Goal

Replace the randomization plot and tables of the thesis (Chapter 7) and of the paper manuscript by numbers for which the trajectory diagnostic (Hellinger distance) and the map diagnostic (map similarity) are computed on **the same randomized models, with the same explanation target, on the full 565-image test split**.

No such run exists yet. The only matched measurement is a 200-image control with two map methods (Section 3).

## 2. What is wrong with the current numbers

All paths are relative to the code repository (`Playing_The_Network_Backward_Official_Repository`, also the `code/` folder of the private paper repository).

1. **Different layers on ViT-B/16.** Both cascades take their layer list from `bwgame/evaluation/metrics/sanity_check.py::_get_randomizable_layers` (every `nn.Linear` and `nn.Conv2d`, output to input).
   - `experiments/sanity_check_randomization/run.py::_build_model` first calls `decompose_composites(model)`. Each `nn.MultiheadAttention` becomes separate `q_proj`, `k_proj`, `v_proj` layers, which enter the list: **74 layers**, archived at steps with 1, 7, 13, ..., 61, 74 randomized layers.
   - `experiments/hellinger_randomization/run.py::_build_model` (and `run_double_random.py`) uses the plain torchvision model. The packed `in_proj_weight` / `in_proj_bias` is a parameter, not an `nn.Linear`, so query, key and value are never randomized: **38 layers**.
2. **Different random weights on all three architectures.** `_randomize_layer` draws from the global RNG after one `torch.manual_seed(seed)` per script. The two scripts draw in different order, and attribution methods consume random numbers between steps. The two pipelines therefore never evaluate the same randomized weights, also on VGG-16 and ResNet-50, where the layer sets coincide.
3. **Different explanation targets.** The Hellinger cascade starts from the class predicted by the pretrained model (`_predict_targets`); the map cascade explains the dataset label.
4. **The per-image association joins different models.** `reproduce/diagnostic_figures.py::per_image_corr_rows` (`ALIGNED_STEPS`) correlates, per image, the Hellinger distance at `encoder_layer_11.self_attention.out_proj` (4 randomized layers) with the map similarity at `encoder_layer_11.self_attention.q_proj` (7 randomized layers) on ViT-B/16, and different random draws on the CNNs.

Evidence: the layer lists in `results_summary/diagnostics/{hellinger_randomization,sanity_check_randomization}/avg.csv.gz`.

Affected artifacts:

| Artifact | Generated file | Problem |
|---|---|---|
| Hellinger cascade plot | `figures/plots/sanity_check/hellinger_live_plots.inc.tex` | ViT panel: query/key/value pretrained; predicted-class target |
| Map similarity at the cascade endpoint | `tables/generated/sanity_check_tabular.tex` | ViT block: other layer set than the plot; all blocks: other random weights and target than the plot |
| Per-image association | `tables/generated/per_image_corr_tabular.tex` | Joins different randomized models on all architectures |
| Double-random reference | `tables/generated/double_random_tabular.tex` | ViT rows: query/key/value pretrained in both copies |
| Macros | `tables/generated/diagnostic_numbers.tex` | Derived from the files above |

Not affected: the input-noise experiment (`hellinger_input_noise`), which randomizes no parameters.

## 3. What exists already

- `reproduce/control_diagnostics.py` with `reproduce/control_common.py` computes both diagnostics on identical model objects. Reuse its pieces: `perturb_parameters` (deterministic seed per parameter tensor), `digest_state`, `explain`, `stable_seed`, `load_model`.
- Its result, `results_summary/controls/corrected_vit_randomization.json`, covers ViT-B/16 only, 200 test images, four conditions (identity, head, through `encoder_layer_11.self_attention.out_proj`, endpoint), query/key/value pretrained, dataset-label targets, and two map methods (Gradient, RG anchor; Spearman of absolute maps).
- Reference values of that control, for the regression test in Section 5.4:

| Condition | H (SG) | H (RG) | Gradient map ρ | RG anchor map ρ |
|---|---|---|---|---|
| Head only | 0.7552 | 0.7692 | 0.6576 | 1.0000 |
| Through block-11 output projection | 0.8856 | 0.9151 | 0.6549 | 1.0000 |
| Endpoint | 0.9505 | 0.9627 | −0.0353 | 0.3770 |

- `results_summary/diagnostics/` holds the archived per-image measurements of the current (mismatched) runs: 122,040 Hellinger comparisons and 3,000 double-random rounds. None of them has an undefined survival-conditioned distance.

## 4. Repositories

| Repository | Role | What you may change |
|---|---|---|
| Code repository (public) | Code and result summaries | Code, tests, `results_summary/diagnostics_matched/` |
| Paper repository (private; the user gives you its location) | Manuscript and its `code/` copy | Only generated tables and figure data, and a results report. No prose. Follow its own cluster rules: nothing cluster-specific in commits, cluster files in its git-ignored folder |
| Thesis repository (this one, public) | Thesis sources | **Nothing.** The workstation has uncommitted edits under `tex/`. Deliver generated files through the code repository; integration happens on the workstation |

## 5. Rerun specification

### 5.1 One shared cascade

- **R1. Deterministic models.** One function returns the randomized state for `(model, variant, seed, step)`. Seed every parameter tensor from `(seed, full parameter name)` as `control_common.perturb_parameters` does. No global RNG. Use seed 42.
- **R2. One layer order.** Use the order of `_get_randomizable_layers` on the decomposed model, so step indices match the archived map cascade.
- **R3. Same weights for both diagnostics.** If `HellingerDiagnostic` needs the plain torchvision model, write the randomized query/key/value weights into the packed `in_proj_weight` / `in_proj_bias` (rows `[0:d]`, `[d:2d]`, `[2d:3d]`). At every evaluated step assert that the plain and the decomposed model give the same logits on a test batch (maximum absolute difference below 1e-4 in float32). Store `digest_state` per step, and assert after each step that no diagnostic changed the model.
- **R4. One target.** The dataset label for both diagnostics, as in the benchmark and in the 200-image control.
- **R5. Same images.** The 565-image test split (`reproduce.common.imagenet_s_split`, seed 42), in the same order.
- **R6. Survival conditioning per image.** Record `survival_mass_A` and `survival_mass_B` for every comparison. Evaluate the survival-conditioned distance so that one undefined comparison cannot remove others (batch size 1, or handle the cutoff per sample instead of per batch). Report the number of undefined comparisons per model, game and step.
- **R7. Paired stochastic methods.** SmoothGrad, LIME, KernelSHAP and DAVE must see the same noise or perturbations on the pretrained and on the randomized model: seed them per `(image, method)` as `control_common.explain` does.

### 5.2 Variants

| Variant | Layers randomized | Models | Purpose |
|---|---|---|---|
| `full` | The whole list, including query, key and value | VGG-16, ResNet-50, ViT-B/16 | Primary result (standard cascading randomization) |
| `qkv_pretrained` | The list without `q_proj`, `k_proj`, `v_proj` | ViT-B/16 only | Convention of the current plot and of the 200-image control; shows how much the convention matters |

Which variant becomes the reported one is the authors' decision once both are available. Recommendation: `full`.

### 5.3 Measurements, per variant

- **M1. Hellinger cascade.** Both games (`adf` = Stopping Game, `rg` = Routing Game at τ = 1), plain and survival-conditioned, all 565 images. All steps if the budget allows. Minimum for ViT-B/16: every step inside encoder block 11, then the block boundaries, then the endpoint.
- **M2. Map similarity.** At the cascade endpoint, for every method row of the current table:
  - ViT-B/16: `gradient__fixed`, `smoothgrad__loc`, `intgrad__loc`, `lrp_eps__loc`, `lrp_gamma__loc`, `attnlrp__loc`, `dave__loc`, `tibav__fixed`, `gae__fixed`, `ar__loc`, `lime__fixed`, `kernelshap__fixed`, `rg__anchor`, `rg__loc`.
  - VGG-16: `gradient__fixed`, `smoothgrad__loc`, `intgrad__loc`, `deeplift__fixed`, `lrp_eps__loc`, `lrp_gamma__loc`, `gcam__fixed`, `gcampp__fixed`, `lcam__fixed`, `lime__fixed`, `kernelshap__fixed`, `sg__loc`, `rg__anchor`, `rg__loc`.
  - ResNet-50: as VGG-16 without `sg__loc`.
  - Metrics as archived: `spearman_abs`, `hog_pearson`, `spearman`, `ssim` (`compute_similarity`).
  - At the 12 archived steps as well, for all methods if affordable, otherwise for `gradient__fixed` and `rg__anchor`.
- **M3. Per-image association.** At one step per model, taken from the variant's own list: VGG-16 `features.26`, ResNet-50 `layer4.1.conv3`, ViT-B/16 the last layer of encoder block 11 (`...q_proj` for `full`, `...out_proj` for `qkv_pretrained`). Per image: the four distances (plain and survival-conditioned, both games) and the Gradient and RG-anchor map similarities (`spearman_abs`, `hog_pearson`). Report the 8×8 Spearman matrix and bootstrap intervals (10,000 resamples) for the distance-versus-map block.
- **M4. Double-random reference.** 500 rounds, two independently randomized copies at the variant's endpoint, one test image per round with the existing seed, both games, plain and survival-conditioned.
- **M5. Prediction audit.** Top-1 accuracy and mean target probability of the randomized model at every evaluated step.

### 5.4 Checks before the long run

1. `pytest -q`, including `tests/test_hellinger_merged_attention.py`.
2. Identity step: distance 0 and map similarity 1 for every method.
3. Regression: variant `qkv_pretrained`, the 200 control images, must reproduce the table in Section 3 to four decimals.
4. The logit and hash assertions of R3.
5. A smoke run of every measurement on 2 images and 2 steps.

### 5.5 Outputs

Write into `results_summary/diagnostics_matched/<variant>/` of the code repository:

- `hellinger_randomization/{per_image.csv.gz, avg.csv.gz}`: the archived columns plus `survival_mass_A`, `survival_mass_B`, `target`, `state_sha256`.
- `sanity_check_randomization/{per_image.csv.gz, avg.csv.gz}`: the archived columns plus `state_sha256`.
- `double_random/{per_round.csv.gz, aggregate.csv.gz}` and `prediction_audit.csv`.
- `MANIFEST.json`: variant, seed, layer list per model, state hash per step, code commit, library versions, number of undefined survival-conditioned comparisons per condition.
- `tables/`: the output of `python -m reproduce.diagnostic_figures` for this variant (tables, macros, plot file). `ALIGNED_STEPS` must take both steps from the same variant. Do not overwrite the generated files of either manuscript before the authors have seen the numbers.

Commit only summaries (CSV, JSON, generated TeX). No maps, datasets, weights, caches or cluster files.

## 6. Integration after the run

Files that the new tables and plot replace:

| Target | Files |
|---|---|
| Code repository | `results_summary/diagnostics/` (after approval), README table |
| Paper repository | `tables/generated/{sanity_check_tabular, per_image_corr_tabular, double_random_tabular, diagnostic_numbers}.tex` and `figures/plots/sanity_check/hellinger_live_plots.inc.tex` of the current manuscript folder. The two `corrected_vit_*` tables become redundant |
| Thesis repository | `tex/tables/ptnb_v2/generated/{sanity_check_tabular, per_image_corr_tabular, double_random_tabular, diagnostic_numbers}.tex`, `tex/figures/ptnb_v2/plots/sanity_check/hellinger_live_plots.inc.tex`, `tex/tables/rebuttal/corrected_vit_randomization_tabular.tex`. `tex/tables/ptnb_v2/sanity_check_blocks.tex` is derived from the first file and must be rebuilt |

Prose that quotes these numbers and must be updated by the authors afterwards:

- Thesis: Chapter 7 (Sections 7.1 and 7.3, the matched-model paragraph and table, the double-random paragraph), the introduction paragraph on the trajectory perspective, the conclusion.
- Paper: the randomization section, the randomization appendix, and the abstract and introduction sentences on trajectory changes.

## 7. Order of work

1. Implement the shared cascade and the checks of Section 5.4.
2. ViT-B/16 `full`: M1, M2 at the endpoint, M3, M5.
3. VGG-16 and ResNet-50: M1, M2 at the endpoint, M3, M5.
4. ViT-B/16 `qkv_pretrained`: M1, M2 at the endpoint, M3, M5.
5. M4 for all models and variants, then M2 at the remaining steps.

Push after every stage.

## 8. Report back

Add `results_summary/diagnostics_matched/REPORT.md` to the code repository with:

- what ran and with which code commit, and every deviation from this specification;
- a table of every number currently quoted in the two manuscripts next to its new value, for both variants;
- the count of undefined survival-conditioned comparisons;
- open problems.
