# Installing Agda

The best method for installing Agda will depend on what operating
system you are using. The [official documentation] gives a lot of
details, but below we have listed some simplified instructions that
worked for us.

[official documentation]: https://agda.readthedocs.io/en/latest/getting-started/installation.html

::: Caution:
Double check the version number by running `agda --version`, if you
install Agda via a package manager. These notes were written against
Agda version `2.8.0`. The exercise files may not work with earlier or
later versions.
:::

::: Caution:
These lecture notes do **not** rely on the the Agda standard library,
and so you don't need to worry about downloading and installing it.
:::

## On Mac via Homebrew

Install the [Homebrew](https://brew.sh/) package manager, then run

``` shell
brew install agda
```

At the time of writing this installs the correct version of Agda, but
it may not in the future!

## On Windows via Stack 

Install Stack from <https://docs.haskellstack.org/en/stable/install_and_upgrade/>

Open PowerShell, and use Stack to install the correct version of Agda:

``` shell
stack --resolver lts-24.4 install Agda
```

This may take a while.


# Installing VSCode

Install [VSCode] and then the [`agda-mode` extension]. If your key
combinations (like `C-c C-c`) don't work, you may need to apply the
fix described [here].

[VSCode]: https://code.visualstudio.com/
[`agda-mode` extension]: https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode
[here]: https://github.com/banacorn/agda-mode-vscode/issues/132#issuecomment-1368880358

Depending on how you installed Agda, you may need to tell VSCode where
the `agda` executable is located. This is under `Preferences >
Extensions` and then the `Agda Mode > Connection: Agda Path` option.

You will want to go `File -> Preferences -> Settings -> Text Editor ->
Suggestions`, and disable `Inline Suggest`. This feature gives AI
suggested snippets of code as you type, but unfortunately, for Agda
these snippets are often confusing and wrong.


# Installing Emacs on Mac

On Mac, you can use Homebrew to install Emacs.

``` shell
brew tap d12frosted/emacs-plus
brew install emacs-plus
agda --emacs-mode=setup
```

Now try running `emacs` in the terminal. If a nice Emacs window
doesn't appear, run

``` shell
brew link --overwrite emacs-plus
```
