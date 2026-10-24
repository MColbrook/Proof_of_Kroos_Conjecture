# Submitting to Palomar

The submission title is **A proof of Kroó’s conjecture**, set by `project.name` in [formalization.yaml](../formalization.yaml). The entry covers the thirteen principal results and their conjunction selected by [comparator.json](../comparator.json).

These instructions follow the official [submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md), [submission form](https://submit.palomar-registry.org/), and [full preflight instructions](https://submit.palomar-registry.org/llms.txt), checked on 24 October 2026.

## 1. Make the repository public

At [the repository settings](https://github.com/MColbrook/Proof_of_Kroos_Conjecture/settings), open **General → Danger Zone → Change repository visibility**, choose **Public**, and complete GitHub's confirmation.

The paper does not need to be uploaded. The repository provides the mathematical statements, proofs, and required metadata.

## 2. Run the full mechanical preflight

Open [Actions](https://github.com/MColbrook/Proof_of_Kroos_Conjecture/actions), select **Palomar preflight**, and choose **Run workflow** on `main`. Wait for both jobs to finish successfully, then inspect the uploaded mechanical report and confirm `status: pass`.

The [workflow](../.github/workflows/palomar-preflight.yml) calls Palomar's reusable verifier at a fixed revision, using `mode: full` and `execution_profile: palomar-standard-v1`. It selects `comparator.json` and declares that the submitter is a responsible author or maintainer. Run it on that basis.

The separate **Verify formalization** workflow checks the repository's build and independent kernels. It does not replace the full Palomar preflight. A passing preflight checks mechanics; it does not perform Palomar's editorial review or register an entry.

Copy the full 40-character commit SHA checked by the successful run. For the current local revision, this is:

```sh
git rev-parse HEAD
```

Use that exact commit throughout submission. If the source or metadata changes, commit and push the changes, then run the preflight for the new revision.

## 3. Complete the submission form

Open [submit.palomar-registry.org](https://submit.palomar-registry.org/) and enter:

| Form field | Value |
|---|---|
| Repository | `MColbrook/Proof_of_Kroos_Conjecture` |
| Commit | The full 40-character SHA from the successful preflight |
| Comparator configuration | `comparator.json` |
| Project directory | Leave blank: the project is at the repository root |
| Formalization metadata | Leave blank: the default is `formalization.yaml` |
| Existing Palomar ID | Leave blank for the first registration |
| Your relationship | **I am a responsible author or maintainer of it** |
| Approval explanation | Leave blank when submitting as the responsible author or maintainer |
| Notes | Optional; may be left blank |

Check the preview title **A proof of Kroó’s conjecture**, the project abstract, and the selected declarations `VerifiedPaper.t01`–`VerifiedPaper.t13` plus `VerifiedPaper.all_principal`. Address any reported preliminary failures before continuing. The Challenge's length may produce an auditability warning; it remains within the hard limits.

Choose **Authenticate via GitHub and submit**. Complete GitHub sign-in and any first-use authorization yourself, within the form's fifteen-minute window. Keep the resulting submission status link.

## 4. Review and register

Wait for mechanical verification and editorial review. Read the complete review and any findings on the status page. If a revision is required, fix the reported issue, commit and push it, repeat the full preflight, and follow the service's retry instructions.

When the submission is eligible for registration, choose whether to register after reading the review. Registration publishes the review and creates the registry record. Starting verification alone does not register the result. The submitted repository, commit, configuration path, and any approval explanation are public when verification starts.
