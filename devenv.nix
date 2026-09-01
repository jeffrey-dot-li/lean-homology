{
  pkgs,
  lib,
  config,
  inputs,
  ...
}: {
  env.UV = "1";

  packages = with pkgs; [
    elan
    nodejs # node/npx for the citra PDF-reading MCP server (opencode.json)
  ];

  enterShell = ''
    alias codex="${config.devenv.root}/scripts/codex-lean.sh"
  '';

  git-hooks.hooks = {
    # shellcheck.enable = true;
    # ruff.enable = true;
    # ruff-format.enable = true;
    alejandra.enable = true;
    lake-build = {
      enable = true;
      name = "lake build";
      entry = "${pkgs.bash}/bin/bash -c 'lake build'";
      language = "system";
      pass_filenames = false;
      stages = ["pre-commit"];
    };
  };

  languages = {
    python = {
      package = pkgs.python312;
      libraries = [
      ];
      enable = true;
      uv = {
        enable = true;
      };
      venv.enable = true;
    };
  };
}
