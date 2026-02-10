# Release process

> [!TIP]
> During development already create a draft GitHub Release and write down all relevant changes, so that
> on release you don't have to go in detail through all commits again.

1. Determine the changes since last release, and based on that choose the corresponding SemVer version change
2. Run the ["Publish" workflow](https://github.com/Marcono1234/struson/actions/workflows/publish.yml) on GitHub\
    This will perform the following things:
    - Update the project version
    - Git commit & tag the changes
    - Publish the version to `crates.io`
    - Push the Git changes
3. Create a [GitHub Release](https://github.com/Marcono1234/struson/releases) (respectively publish the existing draft release)\
    Select the newly created Git tag for that.
4. Optional: In case issues reported by other users were fixed, inform them that a new release including the fix has been published.
