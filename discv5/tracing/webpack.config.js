const path = require('path');

module.exports = {
  mode: 'development',
  entry: './src/main.ts',
  module: {
    rules: [
      {
        test: /\.ts$/,
        use: 'ts-loader',
      },
    ],
  },
  resolve: {
    extensions: [
      '.ts', '.js',
    ],
  },
  output: {
    filename: 'bundle.js',
    path: path.join(__dirname, 'public')
  },
  target: ['web', 'es5'],
  devServer: {
    contentBase: 'public',
    open: true
  },
};
