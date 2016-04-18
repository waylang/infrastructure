require 'spec_helper'

describe 'book::common' do
  let(:chef_run) { ChefSpec::SoloRunner.converge(described_recipe) }

  it 'includes infrastructure::common' do
    expect(chef_run).to include_recipe('infrastructure::common')
  end

  it 'installs texlive and related packages' do
    expect(chef_run).to install_package('texlive')
    expect(chef_run).to install_package('texlive-latex-extra')
    expect(chef_run).to install_package('texlive-math-extra')
  end
end
