import setuptools

with open("README.md", "r", encoding="utf-8") as fh:
    long_description = fh.read()

setuptools.setup(
    name="natural2lean",
    version="0.0.3",
    author="Augustin d'Oultremont",
    author_email="augustin.doultremont@outlook.com",
    description="Translation of proofs from Natural Language to Lean",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/Augustindou/natural2lean",
    project_urls={
        "Bug Tracker": "https://github.com/Augustindou/natural2lean/issues",
    },
    classifiers=[
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
    ],
    package_dir={"": "src"},
    packages=setuptools.find_packages(where="src", exclude=["*-old"]),
    python_requires=">=3.9",
    install_requires=[],
    extras_require={
        "dev": [
            "pytest>=3.6",
        ],
    },
)
