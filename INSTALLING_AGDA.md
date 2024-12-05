# Installing Agda

The best method for installing Agda will depend on what operating
system you are using. The [official documentation] gives a lot of
details, but below we have listed some simplified instructions that
worked for us.

[official documentation]: https://agda.readthedocs.io/en/v2.6.4.1/getting-started/installation.html

::: Aside:
Watch out for the version number if you are installing Agda by using a
package manager. We are using Agda version `2.6.4.1`. The exercise
files may not work with earlier or later versions.
:::

## On Mac via Homebrew

Install the [Homebrew](https://brew.sh/) package manager, then run

``` shell
brew install agda
```

At the time of writing this installs the correct version of Agda, but
it may not in the future!

## On Windows via Stack 

Install Stack from [https://docs.haskellstack.org/en/stable/install_and_upgrade/]

Open PowerShell, and use Stack to install the correct version of Agda:
``` shell
stack --resolver lts-22.9 new Agda
stack install Agda-2.6.4.1
```

## On Mac and Linux via Nix 

If installing Agda via `brew` did not work, we have also provided a
Nix shard that will install the correct version of Agda. This will
also install a copy of Emacs, if you would like to use that as your
editor.

First, install the Nix package manager:

Linux:
``` shell
sh <(curl -L https://nixos.org/nix/install) --daemon
```

Mac:
``` shell
sh <(curl -L https://nixos.org/nix/install)
```

Now we need to enable Nix flakes:
``` shell
mkdir -p ~/.config/nix
echo "experimental-features = nix-command flakes" >> ~/.config/nix/nix.conf
```

For a fun series of blog posts on Nix and how to use it, [click this
link](https://ianthehenry.com/posts/how-to-learn-nix/). We won't need
any heavy lifting here, we're just using Nix to install Agda easily.

Now, when you want to work in Agda with Emacs on this project,
navigate to the directory that you cloned this in and run
``` shell
nix develop
```
This might take a while the first time.

# Installing VSCode

Install [VSCode] and then the [`agda-mode` extension]. If your key
combinations (like `C-c C-c`) don't work, you may need to apply the
temporary fix described [here].

[VSCode]: https://code.visualstudio.com/
[`agda-mode` extension]: https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode
[here]: https://github.com/banacorn/agda-mode-vscode/issues/132#issuecomment-1368880358

Depending on how you installed Agda, you may need to tell VSCode where
the `agda` executable is located. This is under `Preferences >
Extensions` and then the `Agda Mode > Connection: Agda Path` option.

# Installing Emacs on Mac

On Mac, you can use Homebrew to install Emacs.
``` shell
brew tap d12frosted/emacs-plus
brew install emacs-plus
agda-mode setup
```

Now try running `emacs` in the terminal. If a nice Emacs window
doesn't appear, run
``` shell
brew link --overwrite emacs-plus
```

Finally, add the following line to your `~/.emacs` file, so that the
literate Agda files are recognised correctly.
``` emacs-lisp
(add-to-list 'auto-mode-alist '("\\.lagda.md\\'" . agda2-mode))
```
