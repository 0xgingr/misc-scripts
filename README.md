# misc-scripts

Personal batch-processing scripts. Pulls structured data on a schedule, runs it through a configurable weighted scoring model, and dispatches notifications for results that clear a threshold.

## Contents

- `core.py` — single self-contained entry point. Loads config, fetches data, runs scoring, sends notifications. No external project modules required.

## Setup

```bash
pip install -r requirements.txt
cp config.example.json config.json
```

Fill in your own values in `config.json` before running.

## Usage

```bash
python core.py
```

Runs once per invocation; schedule externally (cron, systemd timer, etc.) if recurring runs are needed.

## Notes

- Personal project. Not maintained for general use, no support provided.
- No warranty. Use at your own risk.
