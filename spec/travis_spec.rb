require 'spec_helper'

describe 'book::travis' do
  let(:chef_run) { ChefSpec::SoloRunner.converge(described_recipe) }

  it 'includes common' do
    expect(chef_run).to include_recipe('book::common')
  end
end
