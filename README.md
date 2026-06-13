# ScoRev: Hybrid Software Quality Assessment Framework

## Overview

ScoRev is a hybrid software quality assessment framework that combines deterministic static analysis with Large Language Model (LLM)-based semantic review to provide comprehensive software quality evaluation.

The framework assesses source code across three primary quality dimensions:

* Security
* Complexity
* Maintainability

ScoRev integrates a deterministic scoring engine with a knowledge-distilled language model to generate explainable quality scores, code review findings, semantic insights, and actionable recommendations.

---

## Motivation

Traditional static analysis tools provide deterministic and explainable assessments but often lack semantic understanding of source code. Conversely, large language models offer contextual reasoning capabilities but may suffer from inconsistency and hallucinations.

ScoRev bridges this gap by combining the strengths of both approaches within a unified software quality assessment workflow.

---

## Key Features

* Deterministic software quality scoring
* Multi-dimensional quality assessment
* Security vulnerability analysis
* Cyclomatic complexity evaluation
* Maintainability assessment
* Semantic code review generation
* Knowledge-distilled language model
* Explainable and reproducible assessments
* Line-anchored findings and recommendations

---

## Dataset

This repository contains the ScoRev dataset used for training and evaluation.

### Dataset Statistics

| Attribute | Value                    |
| --------- | ------------------------ |
| Format    | JSONL                    |
| Samples   | 8,761                    |
| Language  | Python                   |
| Source    | Open-source repositories |

File:

```text
scorev_clean_full.jsonl
```

Each sample contains source code, deterministic analysis results, and semantic review information used for training and evaluation.

---

## Framework Architecture

ScoRev follows a hybrid architecture:

1. Static Analysis Engine

   * Security assessment
   * Complexity assessment
   * Maintainability assessment
   * Line-anchored findings

2. Semantic Review Model

   * Knowledge-distilled language model
   * Complementary issue detection
   * Recommendations
   * Quality insights

3. Unified Review Output

   * Quality scores
   * Findings
   * Recommendations
   * Semantic explanations

---

## Research Contributions

The project contributes:

* A hybrid static-analysis and LLM-based quality assessment framework.
* A multi-dimensional software quality scoring methodology.
* A large-scale software quality dataset.
* A grounded knowledge distillation pipeline for semantic code review.
* An explainable and reproducible software assessment workflow.

---

## Future Work

Future improvements include:

* Support for additional programming languages.
* Repository-level analysis.
* Retrieval-Augmented Generation (RAG).
* Multi-agent review systems.
* Additional quality dimensions such as reliability and performance.
* Industrial-scale validation and benchmarking.

---

## Citation

If you use this dataset or framework in academic work, please cite the associated ScoRev research paper.

---

## License

This repository is intended for academic and research purposes.
